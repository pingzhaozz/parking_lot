// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::elision::{have_elision, AtomicElisionExt};
use crate::raw_mutex::{TOKEN_HANDOFF, TOKEN_NORMAL};
use crate::util;
use core::{
    cell::Cell,
    sync::atomic::{AtomicUsize, Ordering},
};
use lock_api::{RawRwLock as RawRwLock_, RawRwLockUpgrade};
use parking_lot_core::{
    self, deadlock, FilterOp, ParkResult, ParkToken, SpinWait, UnparkResult, UnparkToken,
};
use std::time::{Duration, Instant};

use std::mem;
use core::cell::UnsafeCell;
use std::thread;

// This reader-writer lock implementation is based on Boost's upgrade_mutex:
// https://github.com/boostorg/thread/blob/fc08c1fe2840baeeee143440fba31ef9e9a813c8/include/boost/thread/v2/shared_mutex.hpp#L432
//
// This implementation uses 2 wait queues, one at key [addr] and one at key
// [addr + 1]. The primary queue is used for all new waiting threads, and the
// secondary queue is used by the thread which has acquired WRITER_BIT but is
// waiting for the remaining readers to exit the lock.
//
// This implementation is fair between readers and writers since it uses the
// order in which threads first started queuing to alternate between read phases
// and write phases. In particular is it not vulnerable to write starvation
// since readers will block if there is a pending writer.

// There is at least one thread in the main queue.
const PARKED_BIT: usize = 0b0001;
// There is a parked thread holding WRITER_BIT. WRITER_BIT must be set.
const WRITER_PARKED_BIT: usize = 0b0010;
// A reader is holding an upgradable lock. The reader count must be non-zero and
// WRITER_BIT must not be set.
const UPGRADABLE_BIT: usize = 0b0100;
// If the reader count is zero: a writer is currently holding an exclusive lock.
// Otherwise: a writer is waiting for the remaining readers to exit the lock.
const WRITER_BIT: usize = 0b1000;
// Mask of bits used to count readers.
const READERS_MASK: usize = !0b1111;
// Base unit for counting readers.
const ONE_READER: usize = 0b10000;

// Token indicating what type of lock a queued thread is trying to acquire
const TOKEN_SHARED: ParkToken = ParkToken(ONE_READER);
const TOKEN_EXCLUSIVE: ParkToken = ParkToken(WRITER_BIT);
const TOKEN_UPGRADABLE: ParkToken = ParkToken(ONE_READER | UPGRADABLE_BIT);


/// Raw reader-writer lock type backed by the parking lot.
/*
#[cfg_attr(
    any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "powerpc64",),
    repr(align(128))
)]
#[cfg_attr(
    any(
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips64",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "sparc",
        target_arch = "hexagon",
    ),
    repr(align(32))
)]
#[cfg_attr(target_arch = "m68k", repr(align(16)))]
#[cfg_attr(target_arch = "s390x", repr(align(256)))]
#[cfg_attr(
    not(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips64",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "sparc",
        target_arch = "hexagon",
        target_arch = "m68k",
        target_arch = "s390x",
    )),
    repr(align(64))
)]
 */
pub struct RawRwLock {
    read_state: AtomicUsize,
    padded: [u8; 120usize],
    write_state: AtomicUsize,
}

#[cfg(feature = "get_offset")]
macro_rules! get_offset {
    ($type:ty, $field:tt) => ({
        let dummy = ::core::mem::MaybeUninit::<$type>::uninit();

        let dummy_ptr = dummy.as_ptr();
        let member_ptr = unsafe{ ::core::ptr::addr_of!((*dummy_ptr).$field) };
        
        member_ptr as usize - dummy_ptr as usize
    })
}
#[cfg(feature = "get_offset")]
struct RwLock<R, T: ?Sized> {
    raw: R,
    data: UnsafeCell<T>,
}

unsafe impl lock_api::RawRwLock for RawRwLock {
    const INIT: RawRwLock = RawRwLock {
        read_state: AtomicUsize::new(0),
        padded : [0; 120],
        write_state: AtomicUsize::new(0),
    };

    type GuardMarker = crate::GuardMarker;

    #[inline]
    fn lock_exclusive(&self) {
        if self
            .write_state
            .compare_exchange_weak(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            let result = self.lock_exclusive_slow(None);
            debug_assert!(result);
        }

        #[cfg(feature = "get_offset")]
        {
            println!("Offset of read_state: {}", get_offset!(RawRwLock, read_state));
            println!("Offset of write_state: {}", get_offset!(RawRwLock, write_state));
            println!("Offset of raw: {}", get_offset!(RwLock<RawRwLock, u32>, raw));
            println!("Offset of data: {}", get_offset!(RwLock<RawRwLock, u32>, data));
        }
        
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        if self
            .write_state
            .compare_exchange(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            self.deadlock_acquire();
            true
        } else {
            false
        }
    }

    #[inline]
    unsafe fn unlock_exclusive(&self) {
        self.deadlock_release();
        if self
            .write_state
            .compare_exchange(WRITER_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_exclusive_slow(false);
    }

    #[inline]
    fn lock_shared(&self) {
        if !self.try_lock_shared_fast(false) {
            let result = self.lock_shared_slow(false, None);
            debug_assert!(result);
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        let result = if self.try_lock_shared_fast(false) {
            true
        } else {
            self.try_lock_shared_slow(false)
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    unsafe fn unlock_shared(&self) {
        self.deadlock_release();
        let read_state = if have_elision() {
            self.read_state.elision_fetch_sub_release(ONE_READER)
        } else {
            self.read_state.fetch_sub(ONE_READER, Ordering::Release)
        };
        let write_state = self.write_state.load(Ordering::Relaxed);
        if (read_state & READERS_MASK == ONE_READER) && ( write_state & WRITER_PARKED_BIT == WRITER_PARKED_BIT) {
            self.unlock_shared_slow();
        }
    }

    #[inline]
    fn is_locked(&self) -> bool {
        let read_state: usize = self.read_state.load(Ordering::Relaxed);
        match read_state & READERS_MASK {
            0 => {
                let write_state: usize = self.write_state.load(Ordering::Relaxed);
                write_state & WRITER_BIT != 0
            }
            // != 0
            _ => true
        }
    }

    #[inline]
    fn is_locked_exclusive(&self) -> bool {
        let write_state = self.write_state.load(Ordering::Relaxed);
        write_state & (WRITER_BIT) != 0
    }
}
/*
unsafe impl lock_api::RawRwLockFair for RawRwLock {
    #[inline]
    unsafe fn unlock_shared_fair(&self) {
        // Shared unlocking is always fair in this implementation.
        self.unlock_shared();
    }

    #[inline]
    unsafe fn unlock_exclusive_fair(&self) {
        self.deadlock_release();
        if self
            .state
            .compare_exchange(WRITER_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_exclusive_slow(true);
    }

    #[inline]
    unsafe fn bump_shared(&self) {
        if self.state.load(Ordering::Relaxed) & (READERS_MASK | WRITER_BIT)
            == ONE_READER | WRITER_BIT
        {
            self.bump_shared_slow();
        }
    }

    #[inline]
    unsafe fn bump_exclusive(&self) {
        if self.state.load(Ordering::Relaxed) & PARKED_BIT != 0 {
            self.bump_exclusive_slow();
        }
    }

}
 */

/*
unsafe impl lock_api::RawRwLockDowngrade for RawRwLock {
    #[inline]
    unsafe fn downgrade(&self) {
        let state = self
            .state
            .fetch_add(ONE_READER - WRITER_BIT, Ordering::Release);

        // Wake up parked shared and upgradable threads if there are any
        if state & PARKED_BIT != 0 {
            self.downgrade_slow();
        }
    }
}

unsafe impl lock_api::RawRwLockTimed for RawRwLock {
    type Duration = Duration;
    type Instant = Instant;

    #[inline]
    fn try_lock_shared_for(&self, timeout: Self::Duration) -> bool {
        let result = if self.try_lock_shared_fast(false) {
            true
        } else {
            self.lock_shared_slow(false, util::to_deadline(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    fn try_lock_shared_until(&self, timeout: Self::Instant) -> bool {
        let result = if self.try_lock_shared_fast(false) {
            true
        } else {
            self.lock_shared_slow(false, Some(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    fn try_lock_exclusive_for(&self, timeout: Duration) -> bool {
        let result = if self
            .state
            .compare_exchange_weak(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            true
        } else {
            self.lock_exclusive_slow(util::to_deadline(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    fn try_lock_exclusive_until(&self, timeout: Instant) -> bool {
        let result = if self
            .state
            .compare_exchange_weak(0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            true
        } else {
            self.lock_exclusive_slow(Some(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }
}

unsafe impl lock_api::RawRwLockRecursive for RawRwLock {
    #[inline]
    fn lock_shared_recursive(&self) {
        if !self.try_lock_shared_fast(true) {
            let result = self.lock_shared_slow(true, None);
            debug_assert!(result);
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_shared_recursive(&self) -> bool {
        let result = if self.try_lock_shared_fast(true) {
            true
        } else {
            self.try_lock_shared_slow(true)
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }
}

unsafe impl lock_api::RawRwLockRecursiveTimed for RawRwLock {
    #[inline]
    fn try_lock_shared_recursive_for(&self, timeout: Self::Duration) -> bool {
        let result = if self.try_lock_shared_fast(true) {
            true
        } else {
            self.lock_shared_slow(true, util::to_deadline(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    fn try_lock_shared_recursive_until(&self, timeout: Self::Instant) -> bool {
        let result = if self.try_lock_shared_fast(true) {
            true
        } else {
            self.lock_shared_slow(true, Some(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }
}

unsafe impl lock_api::RawRwLockUpgrade for RawRwLock {
    #[inline]
    fn lock_upgradable(&self) {
        if !self.try_lock_upgradable_fast() {
            let result = self.lock_upgradable_slow(None);
            debug_assert!(result);
        }
        self.deadlock_acquire();
    }

    #[inline]
    fn try_lock_upgradable(&self) -> bool {
        let result = if self.try_lock_upgradable_fast() {
            true
        } else {
            self.try_lock_upgradable_slow()
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    unsafe fn unlock_upgradable(&self) {
        self.deadlock_release();
        let state = self.state.load(Ordering::Relaxed);
        if state & PARKED_BIT == 0 {
            if self
                .state
                .compare_exchange_weak(
                    state,
                    state - (ONE_READER | UPGRADABLE_BIT),
                    Ordering::Release,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                return;
            }
        }
        self.unlock_upgradable_slow(false);
    }

    #[inline]
    unsafe fn upgrade(&self) {
        let state = self.state.fetch_sub(
            (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT,
            Ordering::Acquire,
        );
        if state & READERS_MASK != ONE_READER {
            let result = self.upgrade_slow(None);
            debug_assert!(result);
        }
    }

    #[inline]
    unsafe fn try_upgrade(&self) -> bool {
        if self
            .state
            .compare_exchange_weak(
                ONE_READER | UPGRADABLE_BIT,
                WRITER_BIT,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .is_ok()
        {
            true
        } else {
            self.try_upgrade_slow()
        }
    }
}

unsafe impl lock_api::RawRwLockUpgradeFair for RawRwLock {
    #[inline]
    unsafe fn unlock_upgradable_fair(&self) {
        self.deadlock_release();
        let state = self.state.load(Ordering::Relaxed);
        if state & PARKED_BIT == 0 {
            if self
                .state
                .compare_exchange_weak(
                    state,
                    state - (ONE_READER | UPGRADABLE_BIT),
                    Ordering::Release,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                return;
            }
        }
        self.unlock_upgradable_slow(false);
    }

    #[inline]
    unsafe fn bump_upgradable(&self) {
        if self.state.load(Ordering::Relaxed) == ONE_READER | UPGRADABLE_BIT | PARKED_BIT {
            self.bump_upgradable_slow();
        }
    }
}

unsafe impl lock_api::RawRwLockUpgradeDowngrade for RawRwLock {
    #[inline]
    unsafe fn downgrade_upgradable(&self) {
        let state = self.state.fetch_sub(UPGRADABLE_BIT, Ordering::Relaxed);

        // Wake up parked upgradable threads if there are any
        if state & PARKED_BIT != 0 {
            self.downgrade_slow();
        }
    }

    #[inline]
    unsafe fn downgrade_to_upgradable(&self) {
        let state = self.state.fetch_add(
            (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT,
            Ordering::Release,
        );

        // Wake up parked shared threads if there are any
        if state & PARKED_BIT != 0 {
            self.downgrade_to_upgradable_slow();
        }
    }
}

unsafe impl lock_api::RawRwLockUpgradeTimed for RawRwLock {
    #[inline]
    fn try_lock_upgradable_until(&self, timeout: Instant) -> bool {
        let result = if self.try_lock_upgradable_fast() {
            true
        } else {
            self.lock_upgradable_slow(Some(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    fn try_lock_upgradable_for(&self, timeout: Duration) -> bool {
        let result = if self.try_lock_upgradable_fast() {
            true
        } else {
            self.lock_upgradable_slow(util::to_deadline(timeout))
        };
        if result {
            self.deadlock_acquire();
        }
        result
    }

    #[inline]
    unsafe fn try_upgrade_until(&self, timeout: Instant) -> bool {
        let state = self.state.fetch_sub(
            (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT,
            Ordering::Relaxed,
        );
        if state & READERS_MASK == ONE_READER {
            true
        } else {
            self.upgrade_slow(Some(timeout))
        }
    }

    #[inline]
    unsafe fn try_upgrade_for(&self, timeout: Duration) -> bool {
        let state = self.state.fetch_sub(
            (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT,
            Ordering::Relaxed,
        );
        if state & READERS_MASK == ONE_READER {
            true
        } else {
            self.upgrade_slow(util::to_deadline(timeout))
        }
    }
}
 */
impl RawRwLock {
    #[inline(always)]
    fn try_lock_shared_fast(&self, recursive: bool) -> bool {
        let write_state = self.write_state.load(Ordering::Relaxed);

        // We can't allow grabbing a shared lock if there is a writer, even if
        // the writer is still waiting for the remaining readers to exit.
        if write_state & WRITER_BIT != 0 {
            // To allow recursive locks, we make an exception and allow readers
            // to skip ahead of a pending writer to avoid deadlocking, at the
            // cost of breaking the fairness guarantees.
            if !recursive  {
                return false;
            }
        }

        let read_state = self.read_state.load(Ordering::Relaxed);

        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && read_state == 0 {
            self.read_state
                .elision_compare_exchange_acquire(0, ONE_READER)
                .is_ok()
        } else if let Some(new_state) = read_state.checked_add(ONE_READER) {
            self.read_state
                .compare_exchange_weak(read_state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        } else {
            false
        }
    }

    #[cold]
    fn try_lock_shared_slow(&self, recursive: bool) -> bool {
        let mut write_state = usize::default();
        let mut read_state = self.read_state.load(Ordering::Relaxed);
        loop {
            write_state = self.write_state.load(Ordering::Relaxed);
            // This mirrors the condition in try_lock_shared_fast
            if write_state & WRITER_BIT != 0 {
                if !recursive || read_state & READERS_MASK == 0 {
                    return false;
                }
            }

            if have_elision() && read_state == 0 {
                match self.read_state.elision_compare_exchange_acquire(0, ONE_READER) {
                    Ok(_) => return true,
                    Err(x) => read_state = x,
                }
            } else {
                match self.read_state.compare_exchange_weak(
                    read_state,
                    read_state
                        .checked_add(ONE_READER)
                        .expect("RwLock reader count overflow"),
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => read_state = x,
                }
            }
        }
    }
/*
    #[inline(always)]
    fn try_lock_upgradable_fast(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);

        // We can't grab an upgradable lock if there is already a writer or
        // upgradable reader.
        if state & (WRITER_BIT | UPGRADABLE_BIT) != 0 {
            return false;
        }

        if let Some(new_state) = state.checked_add(ONE_READER | UPGRADABLE_BIT) {
            self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        } else {
            false
        }
    }

    #[cold]
    fn try_lock_upgradable_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // This mirrors the condition in try_lock_upgradable_fast
            if state & (WRITER_BIT | UPGRADABLE_BIT) != 0 {
                return false;
            }

            match self.state.compare_exchange_weak(
                state,
                state
                    .checked_add(ONE_READER | UPGRADABLE_BIT)
                    .expect("RwLock reader count overflow"),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(x) => state = x,
            }
        }
    }
 */
    #[cold]
    fn lock_exclusive_slow(&self, timeout: Option<Instant>) -> bool {
        let try_lock = |write_state: &mut usize| {
            loop {
                if *write_state & (WRITER_BIT | UPGRADABLE_BIT) != 0 {
                    return false;
                }

                // Grab WRITER_BIT if it isn't set, even if there are parked threads.
                match self.write_state.compare_exchange_weak(
                    *write_state,
                    *write_state | WRITER_BIT,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => *write_state = x,
                }
            }
        };

        // Step 1: grab exclusive ownership of WRITER_BIT
        let timed_out = !self.lock_common(
            timeout,
            TOKEN_EXCLUSIVE,
            try_lock,
            WRITER_BIT | UPGRADABLE_BIT,
        );
        if timed_out {
            return false;
        }

        // Step 2: wait for all remaining readers to exit the lock.
        self.wait_for_readers(timeout, 0)
    }

    #[cold]
    fn unlock_exclusive_slow(&self, force_fair: bool) {
        // There are threads to unpark. Try to unpark as many as we can.
        let callback = |mut new_state, result: UnparkResult| {
            // If we are using a fair unlock then we should keep the
            // rwlock locked and hand it off to the unparked threads.
            if result.unparked_threads != 0 && (force_fair || result.be_fair) {
                if result.have_more_threads {
                    new_state |= PARKED_BIT;
                }
                self.write_state.store(new_state, Ordering::Release);
                TOKEN_HANDOFF
            } else {
                // Clear the parked bit if there are no more parked threads.
                if result.have_more_threads {
                    self.write_state.store(PARKED_BIT, Ordering::Release);
                } else {
                    self.write_state.store(0, Ordering::Release);
                }
                TOKEN_NORMAL
            }
        };
        // SAFETY: `callback` does not panic or call into any function of `parking_lot`.
        unsafe {
            self.wake_parked_threads(0, callback);
        }
    }

    #[cold]
    fn lock_shared_slow(&self, recursive: bool, timeout: Option<Instant>) -> bool {
        let try_lock = |write_state: &mut usize| {
            let mut spinwait_shared = SpinWait::new();
            let mut read_state = self.read_state.load(Ordering::Relaxed);
            loop {
                // Use hardware lock elision to avoid cache conflicts when multiple
                // readers try to acquire the lock. We only do this if the lock is
                // completely empty since elision handles conflicts poorly.
                if have_elision() && read_state == 0 {
                    match self.read_state.elision_compare_exchange_acquire(0, ONE_READER) {
                        Ok(_) => return true,
                        Err(x) => read_state = x,
                    }
                }

                // This is the same condition as try_lock_shared_fast
                if *write_state & WRITER_BIT != 0 {
                    if !recursive || read_state & READERS_MASK == 0 {
                        return false;
                    }
                }

                if self
                    .read_state
                    .compare_exchange_weak(
                        read_state,
                        read_state
                            .checked_add(ONE_READER)
                            .expect("RwLock reader count overflow"),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    return true;
                }

                // If there is high contention on the reader count then we want
                // to leave some time between attempts to acquire the lock to
                // let other threads make progress.
                spinwait_shared.spin_no_yield();
                read_state = self.read_state.load(Ordering::Relaxed);
                *write_state = self.write_state.load(Ordering::Relaxed);
            }
        };
        self.lock_common(timeout, TOKEN_SHARED, try_lock, WRITER_BIT)
    }

    #[cold]
    fn unlock_shared_slow(&self) {
        // At this point WRITER_PARKED_BIT is set and READER_MASK is empty. We
        // just need to wake up a potentially sleeping pending writer.
        // Using the 2nd key at addr + 1
        let addr = self as *const _ as usize + 1;
        let callback = |_result: UnparkResult| {
            // Clear the WRITER_PARKED_BIT here since there can only be one
            // parked writer thread.
            self.write_state.fetch_and(!WRITER_PARKED_BIT, Ordering::Relaxed);
            TOKEN_NORMAL
        };
        // SAFETY:
        //   * `addr` is an address we control.
        //   * `callback` does not panic or call into any function of `parking_lot`.
        unsafe {
            parking_lot_core::unpark_one(addr, callback);
        }
    }
/*
    #[cold]
    fn lock_upgradable_slow(&self, timeout: Option<Instant>) -> bool {
        let try_lock = |state: &mut usize| {
            let mut spinwait_shared = SpinWait::new();
            loop {
                if *state & (WRITER_BIT | UPGRADABLE_BIT) != 0 {
                    return false;
                }

                if self
                    .state
                    .compare_exchange_weak(
                        *state,
                        state
                            .checked_add(ONE_READER | UPGRADABLE_BIT)
                            .expect("RwLock reader count overflow"),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    return true;
                }

                // If there is high contention on the reader count then we want
                // to leave some time between attempts to acquire the lock to
                // let other threads make progress.
                spinwait_shared.spin_no_yield();
                *state = self.state.load(Ordering::Relaxed);
            }
        };
        self.lock_common(
            timeout,
            TOKEN_UPGRADABLE,
            try_lock,
            WRITER_BIT | UPGRADABLE_BIT,
        )
    }

    #[cold]
    fn unlock_upgradable_slow(&self, force_fair: bool) {
        // Just release the lock if there are no parked threads.
        let mut state = self.state.load(Ordering::Relaxed);
        while state & PARKED_BIT == 0 {
            match self.state.compare_exchange_weak(
                state,
                state - (ONE_READER | UPGRADABLE_BIT),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(x) => state = x,
            }
        }

        // There are threads to unpark. Try to unpark as many as we can.
        let callback = |new_state, result: UnparkResult| {
            // If we are using a fair unlock then we should keep the
            // rwlock locked and hand it off to the unparked threads.
            let mut state = self.state.load(Ordering::Relaxed);
            if force_fair || result.be_fair {
                // Fall back to normal unpark on overflow. Panicking is
                // not allowed in parking_lot callbacks.
                while let Some(mut new_state) =
                    (state - (ONE_READER | UPGRADABLE_BIT)).checked_add(new_state)
                {
                    if result.have_more_threads {
                        new_state |= PARKED_BIT;
                    } else {
                        new_state &= !PARKED_BIT;
                    }
                    match self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return TOKEN_HANDOFF,
                        Err(x) => state = x,
                    }
                }
            }

            // Otherwise just release the upgradable lock and update PARKED_BIT.
            loop {
                let mut new_state = state - (ONE_READER | UPGRADABLE_BIT);
                if result.have_more_threads {
                    new_state |= PARKED_BIT;
                } else {
                    new_state &= !PARKED_BIT;
                }
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return TOKEN_NORMAL,
                    Err(x) => state = x,
                }
            }
        };
        // SAFETY: `callback` does not panic or call into any function of `parking_lot`.
        unsafe {
            self.wake_parked_threads(0, callback);
        }
    }

    #[cold]
    fn try_upgrade_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & READERS_MASK != ONE_READER {
                return false;
            }
            match self.state.compare_exchange_weak(
                state,
                state - (ONE_READER | UPGRADABLE_BIT) + WRITER_BIT,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(x) => state = x,
            }
        }
    }

    #[cold]
    fn upgrade_slow(&self, timeout: Option<Instant>) -> bool {
        self.wait_for_readers(timeout, ONE_READER | UPGRADABLE_BIT)
    }

    #[cold]
    fn downgrade_slow(&self) {
        // We only reach this point if PARKED_BIT is set.
        let callback = |_, result: UnparkResult| {
            // Clear the parked bit if there no more parked threads
            if !result.have_more_threads {
                self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
            }
            TOKEN_NORMAL
        };
        // SAFETY: `callback` does not panic or call into any function of `parking_lot`.
        unsafe {
            self.wake_parked_threads(ONE_READER, callback);
        }
    }

    #[cold]
    fn downgrade_to_upgradable_slow(&self) {
        // We only reach this point if PARKED_BIT is set.
        let callback = |_, result: UnparkResult| {
            // Clear the parked bit if there no more parked threads
            if !result.have_more_threads {
                self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
            }
            TOKEN_NORMAL
        };
        // SAFETY: `callback` does not panic or call into any function of `parking_lot`.
        unsafe {
            self.wake_parked_threads(ONE_READER | UPGRADABLE_BIT, callback);
        }
    }

    #[cold]
    unsafe fn bump_shared_slow(&self) {
        self.unlock_shared();
        self.lock_shared();
    }

    #[cold]
    fn bump_exclusive_slow(&self) {
        self.deadlock_release();
        self.unlock_exclusive_slow(true);
        self.lock_exclusive();
    }

    #[cold]
    fn bump_upgradable_slow(&self) {
        self.deadlock_release();
        self.unlock_upgradable_slow(true);
        self.lock_upgradable();
    }
 */
    /// Common code for waking up parked threads after releasing `WRITER_BIT` or
    /// `UPGRADABLE_BIT`.
    ///
    /// # Safety
    ///
    /// `callback` must uphold the requirements of the `callback` parameter to
    /// `parking_lot_core::unpark_filter`. Meaning no panics or calls into any function in
    /// `parking_lot`.
    #[inline]
    unsafe fn wake_parked_threads(
        &self,
        new_state: usize,
        callback: impl FnOnce(usize, UnparkResult) -> UnparkToken,
    ) {
        // We must wake up at least one upgrader or writer if there is one,
        // otherwise they may end up parked indefinitely since unlock_shared
        // does not call wake_parked_threads.
        let new_state = Cell::new(new_state);
        let addr = self as *const _ as usize;
        let filter = |ParkToken(token)| {
            let s = new_state.get();

            // If we are waking up a writer, don't wake anything else.
            if s & WRITER_BIT != 0 {
                return FilterOp::Stop;
            }

            // Otherwise wake *all* readers and one upgrader/writer.
            if token & (UPGRADABLE_BIT | WRITER_BIT) != 0 && s & UPGRADABLE_BIT != 0 {
                // Skip writers and upgradable readers if we already have
                // a writer/upgradable reader.
                FilterOp::Skip
            } else {
                new_state.set(s + token);
                FilterOp::Unpark
            }
        };
        let callback = |result| callback(new_state.get(), result);
        // SAFETY:
        // * `addr` is an address we control.
        // * `filter` does not panic or call into any function of `parking_lot`.
        // * `callback` safety responsibility is on caller
        parking_lot_core::unpark_filter(addr, filter, callback);
    }

    // Common code for waiting for readers to exit the lock after acquiring
    // WRITER_BIT.
    #[inline]
    fn wait_for_readers(&self, timeout: Option<Instant>, prev_value: usize) -> bool {
        // At this point WRITER_BIT is already set, we just need to wait for the
        // remaining readers to exit the lock.
        let mut spinwait = SpinWait::new();
        let mut read_state = self.read_state.load(Ordering::Acquire);
        while read_state & READERS_MASK != 0 {
            // Spin a few times to wait for readers to exit
            if spinwait.spin() {
                read_state = self.read_state.load(Ordering::Acquire);
                continue;
            }

            //
            thread::sleep(Duration::from_millis(1));
            spinwait.reset();
            read_state = self.read_state.load(Ordering::Acquire);

        }
        true
    }

    /// Common code for acquiring a lock
    #[inline]
    fn lock_common(
        &self,
        _timeout: Option<Instant>,
        _token: ParkToken,
        mut try_lock: impl FnMut(&mut usize) -> bool,
        _validate_flags: usize,
    ) -> bool {
        let mut spinwait = SpinWait::new();
        let mut write_state = self.write_state.load(Ordering::Relaxed);
        loop {
            // Attempt to grab the lock
            if try_lock(&mut write_state) {
                return true;
            }

            // If there are no parked threads, try spinning a few times.
            if write_state & (PARKED_BIT | WRITER_PARKED_BIT) == 0 && spinwait.spin() {
                write_state = self.write_state.load(Ordering::Relaxed);
                continue;
            }

            // Loop back and try locking again
            thread::sleep(Duration::from_millis(1));
            spinwait.reset();
            write_state = self.write_state.load(Ordering::Relaxed);
        }
    }

    #[inline]
    fn deadlock_acquire(&self) {
        unsafe { deadlock::acquire_resource(self as *const _ as usize) };
        unsafe { deadlock::acquire_resource(self as *const _ as usize + 1) };
    }

    #[inline]
    fn deadlock_release(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        unsafe { deadlock::release_resource(self as *const _ as usize + 1) };
    }
}
