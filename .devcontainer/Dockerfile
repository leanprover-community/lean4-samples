# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.245.2/containers/ubuntu/.devcontainer/base.Dockerfile

# [Choice] Ubuntu version (use ubuntu-22.04 or ubuntu-18.04 on local arm64/Apple Silicon): ubuntu-22.04, ubuntu-20.04, ubuntu-18.04
ARG VARIANT="jammy"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

RUN apt-get update && apt-get install -yq build-essential nodejs npm

USER vscode
RUN echo $HOME
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSfL | sh -s -- --default-toolchain leanprover/lean4:nightly -y
RUN echo 'export PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile

