FROM ubuntu:latest

# https://code.visualstudio.com/remote/advancedcontainers/add-nonroot-user#_change-the-uidgid-of-an-existing-container-user
ARG USERNAME=ubuntu
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN apt-get update \
    && apt-get install -y openjdk-21-jdk openjdk-21-source \
    build-essential \
    libmsgpack-cxx-dev clang-tools clangd cmake ninja-build \
    wget ssh

RUN wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz
RUN tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz
ENV PATH="$PATH:/usr/local/go/bin:/home/${USERNAME}/go/bin"
RUN go version

ENV EDITOR="code --wait"

RUN groupmod --gid $USER_GID $USERNAME \
    && usermod --uid $USER_UID --gid $USER_GID $USERNAME \
    && mkdir -p /home/$USERNAME \
    && chown -R $USER_UID:$USER_GID /home/$USERNAME

USER $USERNAME
