# Dockerfile
FROM rust:1.76

# 创建 app 目录
WORKDIR /app

# 复制当前目录内容
COPY . .

# 设置默认命令行
#CMD ["cargo", "build"]

# 构建应用
#RUN cargo build --release

# 设置环境变量
#ENV RUST_LOG=info

# 暴露端口
#EXPOSE 8080

# 运行benchmark
#CMD ["cargo", "run", "--release", "--bin", "benchmark"]


