# ProofFrog proof that "KEM+DEM is semantically secure as a PKE"

- Proof engine: [ProofFrog](https://prooffrog.github.io/)
- Proof author: Douglas Stebila

## Worked tutorial

See the [worked tutorial](tutorial/README.md) for a walk-through of the proof.

The original Joy of Cryptography-style proof is available at [https://garbledcircus.com/kemdem/left-right](https://garbledcircus.com/kemdem/left-right)

## Instructions to run

1. Clone this repository: `git clone https://github.com/proof-ladders/asymmetric-ladder.git`

2. Install ProofFrog:

	```sh
	git clone https://github.com/ProofFrog/ProofFrog.git
	cd ProofFrog
	pip3 install -r requirements.txt
	cd ..
	```

3. Run ProofFrog on the proof:

	```sh
	cd asymmetric-ladder/kemdem/ProofFrog/src
	PYTHONPATH=../../../../ProofFrog python3 -m proof_frog prove Hyb-is-CPA.proof
	```

	The last line of the output should say "Proof Succeeded!".  The full expected output can be found in the file `output.txt`.
