FROM mcr.microsoft.com/devcontainers/base:ubuntu

RUN apt-get update \
    && apt-get install -y openjdk-21-jdk openjdk-21-source \
    build-essential \
    libmsgpack-cxx-dev clang-tools clangd cmake ninja-build \
    wget ssh sudo gdb

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin:/home/vscode/go/bin"
RUN go version

ENV EDITOR="code --wait"
