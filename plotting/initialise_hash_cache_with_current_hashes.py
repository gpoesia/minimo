import h5py
import yaml
import influxdb_client
import hashlib
import json
import os
import logging
from influxdb_client.client.write_api import SYNCHRONOUS

logging.basicConfig(level=logging.INFO)

def calculate_file_hash(file_path):
    """Calculate SHA-256 hash of a file."""
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        # Read the file in chunks to handle large files efficiently
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def save_hash_cache(cache_file, cache):
    """Save the hash cache to JSON file."""
    with open(cache_file, 'w') as f:
        json.dump(cache, f, indent=2)

def main():
    # Initialize hash cache
    cache_file = os.path.join(os.path.dirname(__file__), 'hdf5_hashes.json')
    # new hash cache
    hash_cache = {}
    base_dir = os.getenv("EXPERIMENTS_DIR")
    
    # Loop through all experiment directories
    for experiment_name in os.listdir(base_dir):
        experiment_path = os.path.join(base_dir, experiment_name)
        if os.path.isdir(experiment_path):
            logging.info(f"Processing experiment: {experiment_name}")
            try:
                # Get the timestamped directory
                experiment_dirs = [d for d in os.listdir(experiment_path) 
                                if os.path.isdir(os.path.join(experiment_path, d))]
                if not experiment_dirs:
                    logging.warning(f"No experiment directories found in {experiment_path}")
                    continue
                
                # Get the HDF5 file path
                working_dir = os.path.join(experiment_path, experiment_dirs[0])
                log_file = os.path.join(working_dir, "experiment_dir/logs/log_no_seed_provided.hdf5")
                
                if not os.path.exists(log_file):
                    logging.warning(f"No HDF5 file found at {log_file}")
                    continue

                # Get the run name from hydra config
                hydra_yaml = os.path.join(working_dir, ".hydra/hydra.yaml")
                if not os.path.exists(hydra_yaml):
                    logging.warning(f"No hydra.yaml found at {hydra_yaml}")
                    continue

                with open(hydra_yaml, "r") as f:
                    hydra_config = yaml.safe_load(f)
                    run_name = hydra_config["hydra"]["job"]["name"]

                # Calculate hash of the HDF5 file
                current_hash = calculate_file_hash(log_file)
                hash_cache[run_name] = current_hash
                
            except Exception as e:
                logging.error(f"Error processing {experiment_name}: {str(e)}")
                continue

    save_hash_cache(cache_file, hash_cache)
    logging.info(f"Hash cache initialized with {len(hash_cache)} entries")

if __name__ == "__main__":
    main()