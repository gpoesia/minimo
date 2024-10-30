python3 -m venv .venv
source .venv/bin/activate
pip3 install maturin
cd environment
maturin dev --release
cargo build --bin peano --release
cd ../learning
pip3 install -r requirements.txt