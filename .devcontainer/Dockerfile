FROM mcr.microsoft.com/devcontainers/base:noble

RUN apt-get update \
    && apt-get install -y openjdk-21-jdk openjdk-21-source

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin:/home/vscode/go/bin"
RUN go version

USER vscode

RUN mkdir -p /home/vscode \
    && cd /home/vscode \
    && curl -sSLf https://scala-cli.virtuslab.org/get | sh \
    && . ~/.profile \
    && scala-cli version
