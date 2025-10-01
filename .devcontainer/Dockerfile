FROM mcr.microsoft.com/devcontainers/base:ubuntu24.04

# Note: there is no OpenJDK installed. Mill uses its own.
# Look at the top of build.mill to see the most-used version.

RUN apt-get update \
    && apt-get install -y \
    build-essential \
    libmsgpack-cxx-dev clang-tools clangd cmake ninja-build \
    wget ssh sudo gdb \
    python3-dev swig

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin:/home/vscode/go/bin"
RUN go version

ENV EDITOR="code --wait"
