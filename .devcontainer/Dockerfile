FROM mcr.microsoft.com/devcontainers/base:noble

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin"
RUN go version

RUN mkdir -p /home/vscode \
    && cd /home/vscode \
    && su --login vscode -c "curl -sSLf https://scala-cli.virtuslab.org/get | sh" \
    && su --login vscode -c "scala-cli version"
