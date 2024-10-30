#!/bin/bash

LOGLEVEL=""
while [[ $# -gt 0 ]]; do
    case $1 in
        -v|--verbose)
            LOGLEVEL="--loglevel verbose"
            shift
            ;;
    esac
done

# Get a random available port or use a specific one assigned by your cluster
export REDIS_PORT=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
echo "Starting Redis on port $REDIS_PORT"

# Save the port to a file for other processes to read
echo "$(hostname):$REDIS_PORT" > redis_hostname_port.txt

# Cleanup function to remove port file and kill Redis when the script exits
cleanup() {
    rm -f redis_hostname_port.txt
    pkill -f "redis-server --port $REDIS_PORT"
    exit
}

# Set up trap to catch script termination
trap cleanup SIGINT SIGTERM

# Start Redis container in the foreground
apptainer run --env REDIS_PORT=$REDIS_PORT redis.sif redis-server --port $REDIS_PORT --protected-mode no --bind 0.0.0.0 $LOGLEVEL
