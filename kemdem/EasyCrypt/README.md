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

2. Set up EasyCrypt, either following its direct [set up
   guide](https://easycrypt.gitlab.io/easycrypt-web/docs/guides/setting-up-easycrypt)
   or by taking on board the less opinionated discussions available on
   [github](https://github.com/easycrypt/easycrypt).
  a. When choosing SMT solvers to install, be aware that this proof requires Z3
     (>= 4.8). (You can install other solvers, but they will not be used, and
     not having Z3 (>= 4.8) will lead to erros when checking.)
  b. Don't forget to also configure EasyCrypt.

  ```sh
  easycrypt why3config
  ```

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

  A proper run will display:
  - The command being executed;
  - The number of parallel threads being used; (this defaults to the number of
    cores available)
  - For each file being verified, a line displaying a progress bar, settling on
    success to a green tick, followed by the total processing time, followed by
    a filled progress bar, and finally followed by the name of the file;
  - A summary of successes, warnings and failures also indicating overall
    processing time for the whole batch.

## Description of files

The files of interest for the tutorial are in the `left-or-right` folder. This
contains:
- `DEM_lor.eca`: Abstract definitions for syntax and semantic security
  (left-or-right indistinguishability under one-time CPA) of a symmetric
  encryption scheme (or Data Encryption Mechanism);
- `KEM_rork.eca`: Abstract definitions for syntax and real-or-random-key under
  CPA of a Key Encapsulation Mechanism; (this is the standard CPA security
  notion for KEMs)
- `PKE_lor.eca`: Abstract definitions for syntax and left-or-right
  indistinguishability under CPA for public-key encryption;
- `KEMDEM_lor.ec`: An abstract definition of the KEM+DEM construction, and
  a proof that its CPA security as a PKE follows from the security of the KEM
  and that of the DEM. (Lemma `security_of_kem_dem`, along with definitions for
  the reductions involved in the advantage claims: `B_kem_0`, `B_kem_1` and
  `B_s`.)

This folder also contains a standalone file (`KEMDEM.ec`) that contains the
whole proof with specialised definitions (rather than general definitions
instantiated to suit); slightly easier to process as a first tutorial entry
point.
