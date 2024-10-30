#!/bin/bash
# Read the Redis port
export REDIS=$(cat redis_hostname_port.txt)

# Start a Celery worker
cd learning/
celery -A worker worker --concurrency=1 -n $REDIS