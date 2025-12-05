FROM mcr.microsoft.com/devcontainers/base:ubuntu24.04

# Note: there is no OpenJDK needed. Mill uses its own.
# Look at the top of build.mill to see the most-used version.
# The one configured below is just for the VSCode TLA+ tools.

# For build tools / TLC happiness
RUN apt-get update \
    && apt-get install -y clangd gdb openjdk-25-jdk-headless

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin:/home/vscode/go/bin"
RUN go version

ENV EDITOR="code --wait"
