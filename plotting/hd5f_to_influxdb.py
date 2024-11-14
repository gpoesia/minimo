import h5py
import yaml
import influxdb_client
import math
import logging
import numpy as np
from influxdb_client.client.write_api import SYNCHRONOUS, Point
from datetime import datetime
import os
import json
import hashlib

logging.basicConfig(level=logging.INFO)

# FIXME: influxdb port is hardcoded
# FIXME: bucket name is hardcoded
# FIXME: org name is hardcoded

def calculate_file_hash(file_path):
    """Calculate SHA-256 hash of a file."""
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        # Read the file in chunks to handle large files efficiently
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def load_hash_cache(cache_file):
    """Load the hash cache from JSON file."""
    try:
        with open(cache_file, 'r') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}

def save_hash_cache(cache_file, cache):
    """Save the hash cache to JSON file."""
    with open(cache_file, 'w') as f:
        json.dump(cache, f, indent=2)

def process_experiment(experiment_path, client, write_api, bucket, org, hash_cache, cache_file):
    """Process a single experiment directory and write its data to InfluxDB."""
    # Get the actual experiment directory (the timestamped folder)
    experiment_dirs = [d for d in os.listdir(experiment_path) if os.path.isdir(os.path.join(experiment_path, d))]
    if not experiment_dirs:
        logging.warning(f"No experiment directories found in {experiment_path}")
        return
    
    working_dir = os.path.join(experiment_path, experiment_dirs[0])
    log_file = os.path.join(working_dir, "experiment_dir/logs/log_no_seed_provided.hdf5")
    hydra_yaml = os.path.join(working_dir, ".hydra/hydra.yaml")
    config_yaml = os.path.join(working_dir, ".hydra/config.yaml")

    # Skip if required files don't exist
    if not all(os.path.exists(f) for f in [log_file, hydra_yaml, config_yaml]):
        logging.warning(f"Missing required files in {working_dir}")
        return

    # Calculate current file hash
    current_hash = calculate_file_hash(log_file)
    
    with open(hydra_yaml, "r") as f:
        hydra_config = yaml.safe_load(f)
        run_name = hydra_config["hydra"]["job"]["name"]
    with open(config_yaml, "r") as f:
        config = yaml.safe_load(f)
        num_train_iterations = config["agent"]["policy"]["train_iterations"]

    # Check if hash has changed
    if run_name in hash_cache and hash_cache[run_name] == current_hash:
        logging.info(f"No changes detected for {run_name}, skipping...")
        return

    with h5py.File(log_file, "r") as f:
        data = f["no_seed_provided"]
        stats = data["stats"]
        time = data["time"]
        
        timestamps = time["time"][:]
        timestamps = [timestamp.decode("utf-8") for timestamp in timestamps]
        timestamp_indices = np.arange(len(timestamps))
        
        # Create a mask that specifies which timestamps correspond to iteration metrics
        # The first num_train_iterations entries should be False, hence the -(num_train_iterations-1)
        iteration_mask = ((timestamp_indices-(num_train_iterations-1)) % num_train_iterations == 0)
        
        iteration_counter = 0
        step_counter = 0
        for idx, timestamp in enumerate(timestamps):
            timestamp = datetime.strptime(timestamp, "%y-%m-%d/%H:%M")

            if iteration_mask[idx]:
                point_dict = {
                    "measurement": run_name,
                    "time": timestamp,
                    "fields": {}
                }
                
                fields = {
                    "num_iterations": time["num_iterations"][iteration_counter],
                    "val_loss": stats["val_loss"][iteration_counter],
                    "final_goals_proven": stats["final_goals_proven"][iteration_counter],
                    "ratio_proven": stats["ratio_proven"][iteration_counter],
                    "mean_hard_sol_log_probs": stats["mean_hard_sol_log_probs"][iteration_counter]
                }
                iteration_counter += 1
            else:
                point_dict ={
                    "measurement": run_name,
                    "time": timestamp,
                    "fields": {}
                }

                fields = {
                    "num_steps": time["num_steps"][step_counter],
                    "loss": stats["loss"][step_counter],
                    "train_loss": stats["train_loss"][step_counter],
                    "progress_loss": stats["progress_loss"][step_counter],
                    "mu": stats["mu"][step_counter],
                    "ratio_diff_problem_pairs": stats["ratio_diff_problem_pairs"][step_counter]
                }
                step_counter += 1

            for metric, value in fields.items():
                try:
                    value = float(value)
                    if not (math.isnan(value) or math.isinf(value)):
                        point_dict["fields"][metric] = value
                except (ValueError, TypeError):
                    logging.warning(f"Error processing metric {metric} with value {value}")
                    continue
                
            if point_dict["fields"]:
                point = Point.from_dict(point_dict)
                write_api.write(bucket=bucket, record=point)
                logging.debug(f"Wrote point {point}")

        # Update hash cache after successful processing
        hash_cache[run_name] = current_hash
        save_hash_cache(cache_file, hash_cache)
        logging.info(f"Updated hash cache for {run_name}")

def main():
    # Configure InfluxDB client
    org = "p(doom)"
    client = influxdb_client.InfluxDBClient(
        url="http://localhost:8086",
        token=os.getenv("INFLUXDB_TOKEN"),
        org=org
    )
    write_api = client.write_api(write_options=SYNCHRONOUS)
    bucket = "standard-bucket"

    # Initialize hash cache
    cache_file = os.path.join(os.path.dirname(__file__), 'hdf5_hashes.json')
    hash_cache = load_hash_cache(cache_file)

    # should end with `outputs/`
    base_dir = os.getenv("EXPERIMENTS_DIR")
    
    # Loop through all experiment directories
    for experiment_name in os.listdir(base_dir):
        experiment_path = os.path.join(base_dir, experiment_name)
        if os.path.isdir(experiment_path):
            logging.info(f"Processing experiment: {experiment_name}")
            try:
                process_experiment(experiment_path, client, write_api, bucket, org, hash_cache, cache_file)
            except Exception as e:
                logging.error(f"Error processing {experiment_name}: {str(e)}")
                continue

    client.close()

if __name__ == "__main__":
    main()