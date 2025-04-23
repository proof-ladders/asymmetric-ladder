# EasyCrypt proof that "KEM+DEM is semantically secure as a PKE"

- Proof engine: [EasyCrypt](https://easycrypt.info/)
- Proof author: François Dupressoir

## Worked tutorial

TODO

The proof as currently formalized mainly follows [Boneh and
Shoup](https://toc.cryptobook.us/) (see Exercise 11.9 of version 0.6), with
some game-based structuring.

## Instructions to run

1. Clone this repository: `git clone https://github.com/proof-ladders/asymmetric-ladder.git`

2. [Install EasyCrypt](https://github.com/easycrypt/easycrypt)
  a. Install Z3 (>= 4.8)
  b. Install python's `curses` module (using your preferred method).

  ```sh
  easycrypt why3config
  ```

  c. Configure EasyCrypt

3. Run EasyCrypt on the proof:

	```sh
	cd asymmetric-ladder/kemdem/EasyCrypt
  easycrypt runtest proofs.config left-or-right
	```

  This tells EasyCrypt to use the configuration options for scenario
  `left-or-right`, as specified in file `proofs.config`. In our case, the
  configuration is minimal: we simply specify which folder the proof files are
  found in.
  Additional configuration is also provided through `easycrypt.project`, which
  specify the minimum set and version of provers we expect for this proof.
  EasyCrypt will fail without running if those constraints are not met.

----

This folder also contains a standalone file that contains the whole proof with
specialised definitions (rather than general definitions instantiated to suit).
