#!/bin/bash

# Create directory for Redis installation
mkdir -p ~/redis
cd ~/redis

# Download Redis source code (using version 7.2 to match the Docker version)
wget https://download.redis.io/releases/redis-7.2.0.tar.gz
tar xzf redis-7.2.0.tar.gz
cd redis-7.2.0

# Compile Redis
make

# Add Redis binaries to PATH (add this to your ~/.bashrc or ~/.profile)
echo 'export PATH=$PATH:$HOME/redis/redis-7.2.0/src' >> ~/.bashrc
source ~/.bashrc