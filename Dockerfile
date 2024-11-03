# Use Python 3.11 as base image
FROM nvcr.io/nvidia/pytorch:24.01-py3

# Install Rust and cargo
RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    && curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Add cargo to PATH
ENV PATH="/root/.cargo/bin:${PATH}"

# Set working directory
WORKDIR /app

# Copy your project files
COPY . .

# Install uv
RUN pip install uv

# Create and activate virtual environment, install dependencies
RUN uv sync \
    && python -m ensurepip --upgrade \
    && pip install maturin

# Build the Rust components
WORKDIR /app/environment
RUN maturin build --release \
    && cargo build --bin peano --release

# Install Python requirements
WORKDIR /app/learning
RUN pip install -r requirements.txt

# Set working directory back to root
WORKDIR /app

# Add an entrypoint or CMD based on how you run your application
# CMD ["python", "your_main_script.py"]