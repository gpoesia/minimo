# Install uv
curl -LsSf https://astral.sh/uv/install.sh | sh

# Create a virtual environment with python 3.11 and install pip3
uv sync
source .venv/bin/activate
python3 -m ensurepip --upgrade

pip3 install maturin
cd environment
maturin dev --release
cargo build --bin peano --release
cd ../learning
pip3 install -r requirements.txt