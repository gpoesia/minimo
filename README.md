# Learning Formal Mathematics From Intrinsic Motivation

This is the implementation of the following paper:

```bibtex
@article{poesia2024learning,
  title={Learning Formal Mathematics From Intrinsic Motivation},
  author={Poesia, Gabriel and Broman, David and Haber, Nick and Goodman, Noah D},
  journal={arXiv preprint arXiv:2407.00695},
  year={2024}
}
```

You can find it on [arXiv](https://arxiv.org/abs/2407.00695). This repository builds on the [original Peano code base](https://github.com/gpoesia/peano), though it stands alone.

### Compiling the environment

The Peano enviroment is written in Rust and has a Python API via [PyO3](https://pyo3.rs/v0.18.2/).

To compile it, you'll first need to install the Rust toolchain. For that, use [rustup](https://rustup.rs/).

The environment compiles two targets: a `peano` binary, that can be used stand-alone, as well as a `peano` Python library, which we'll use to interact with agents. To build, we'll use `maturin`, a PyO3 build system. Make sure you have Python version at least 3.9. Then, first make a Python virtual environment (conda works too):

```sh
[peano] $ python -m venv /path/to/new/virtual/environment
[peano] $ source /path/to/new/virtual/environment/bin/activate
```

Now, within your environment, install maturin with:

```sh
[peano] $ pip install maturin
```

With `maturin` you can now compile both the Peano environment and library with it:

```sh
[peano] $ cd environment
[environment] $ maturin dev --release  # This will compile the Peano library.
[...]
[environment] $ cargo build --bin peano --release  # This compiles the peano executable.
```

This should eventually terminate. It will produce a `peano` executable,
which you can test on some example proofs:

```sh
[environment]$ target/release/peano theories/natural_number_game.p t_example1
Loading theories/natural_number_game.p
Verifying t_example1... ok
[environment]$
```

You should also now have a `peano` Python module that you can import:

```sh
[environment]$ python
>>> import peano
>>>
```

If this works without errors, you're ready to use Peano from Python. Before running any scripts, make sure to install dependencies with:

```sh
[environment] $ cd ../learning
[learning] $ pip install -r requirements.txt
```
# Peano Tutorial

For an introduction to the Peano language, you can follow the [tutorial](tutorial.md).

To check some more comprehensive examples of proofs in Peano, you're encouraged to take a look at some manually written solutions for the [Natural Number Game](environment/theories/natural_number_game.p).

# Python API Tutorial

This will come soon - I will write a simple example of loading the environment, loading a background theory, setting a theorem statement as a goal, running proof search and reconstructing the proof.

# Running the experiments

The entry point for the conjecture-prove loop is in [learning/bootstrap.py](bootstrap.py). It should suffice to pass it one of the domain configuration files, such as:

```sh
[learning] $ python bootstrap.py theory=groups
```

We use hydra for configuration -- the relevant file here is [config/bootstrap.yaml](config/bootstrap.yaml). This will run the loop in "sequential" mode, in a single process. There is a distributed mode, backed by a [https://docs.celeryq.dev/en/stable/](Celery queue), that you can use to leverage multiple CPUs/GPUs, either in the same or different machines (it doesn't matter, as long as they can connect to the queue). The setup is a bit manual: you must first spin up a Redis server, then run Celery worker processes backed by the Redis server, and finally run bootstrap.py with a DISTRIBUTED=1 environment variable:

```sh
[learning] $ DISTRIBUTED=1 python bootstrap.py theory=groups
```

Feel free to open an issue if you're interested in setting this up, and I can expand on the documentation. The details might get a little bit cluster-specific, though the general setup is just that you need (a) a Redis server, (b) a number of worker processes that connect to it, and (c) a teacher process that runs the bootstrapping loop, also connecting to the same Redis server.
