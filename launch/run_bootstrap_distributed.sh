#!/bin/bash
# Read the Redis port
export REDIS=$(cat redis_hostname_port.txt)
export DISTRIBUTED=1

# Run the bootstrap script
cd learning/
python bootstrap.py $@