import subprocess
from itertools import product
import os

filename = "benchmark"

# Then we loop through realistic programs to compare e2e time for SP1 vs. Risc0.
os.environ["NO_GROTH16"] = "true"
os.environ["RECONSTRUCT_COMMITMENTS"] = "true"

trials = 1
# options_program = ["fibonacci", "sha2-chain", "tendermint"]
# options_program = ["fibonacci", "sha2-chain"]
options_program = ["fibonacci"]
# options_program = ["reth"]
# options_prover = ["sp1"]
# options_prover = ["risc0"]
options_prover = ["sp1", "risc0"]
# options_prover = ["jolt-zkvm"]
options_hashfn = ["poseidon"]
# options_shard_size = [20, 21, 22]
# options_shard_size = [21]
options_shard_size = [22]

# Generate the Cartesian product of the options
option_combinations = product(
    options_program, options_prover, options_hashfn, options_shard_size
)

# Run the shell script with each combination of options
for program, prover, hashfn, shard_size in option_combinations:
    first_shard_size = options_shard_size[0]
    if (
        prover != "sp1" and shard_size != first_shard_size
    ):  # Only sp1 supports different shard sizes
        continue
    print(program, prover, hashfn, shard_size)
    for i in range(trials):
        subprocess.run(
            ["bash", "eval.sh", program, prover, hashfn, str(shard_size), filename]
        )
