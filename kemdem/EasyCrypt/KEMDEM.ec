(*^
  As specified in Boneh and Shoup's "Graduate Course in Applied Cryptography"
  https://toc.cryptobook.us/
  (Exercise 11.9 of version 0.6.)
^*)
require import AllCore Distr.

(*^
  A more mature proof would rely on libraries of definitions.
  Generic definitions have a lot more parameters than what
  we'd like to expose a tutorial reader to.

  Instead, we inline (and specialize) the definitions we care about.
^*)

(*
  Given sets of public keys, secret keys, symmetric (DEM) keys,
  KEM ciphertexts, plaintexts, and DEM ciphertexts ...
*)
type pkey, skey, key, kct, pt, dct.

(* ... and the uniform distribution over the set of symmetric (DEM) keys *)
op [lossless full uniform] dkey : key distr.


(**
  A KEM is a triple of (potentially probabilistic and stateful)
  algorithms:
**)
module type KEM = {
  proc keygen(): pkey * skey
  proc encaps(pk : pkey): key * kct
  proc decaps(sk : skey, k : kct): key option
}.

(** A CPA adversary against the KEM is an algorithm: **)
module type KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, c : kct): bool
}.

(**
  And we define the advantage of a CPA adversary A against a KEM E
  as
    `|   Pr[KEM_CPA_Exp(E, A).run(false) @ &m: res]
       - Pr[KEM_CPA_Exp(E, A).run(true) @ &m: res]  |
  where KEM_CPA_Exp is the experiment:
**)
module KEM_CPA_Exp (E : KEM) (A : KEM_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, k0, k1, c, b';

    (pk, sk) <@ E.keygen();
    (k0, c) <@ E.encaps(pk);
    k1 <$ dkey;
    b' <@ A.distinguish(pk, if b then k1 else k0, c);
    return b';
  }
}.

(**
  A DEM is a pair of algorithms:
  (We force key generation to be sampling from `dkey`.)
**)
module type DEM = {
  (* Normally, we put something like `proc keygen() : key` here *)
  proc enc(k : key, m : pt): dct
  proc dec(k : key, c : dct): pt
}.

(** A passive/eavesdropping DEM adversary is a pair of algorithms: **)
module type DEM_1CPA_Adv = {
  proc choose(): pt * pt
  proc distinguish(c : dct): bool
}.

(**
  And we define the advantage of a passive adversary A against a DEM
  as
    `|   Pr[DEM_1CPA_Exp(E, A).run(false) @ &m: res]
       - Pr[DEM_1CPA_Exp(E, A).run(true) @ &m: res]  |
  where DEM_1CPA_Exp is the experiment:
**)
module DEM_1CPA_Exp (E : DEM) (A : DEM_1CPA_Adv) = {
  proc run(b : bool) = {
    var k, m0, m1, c, b';

    k <$ dkey;
    (m0, m1) <@ A.choose();
    c <@ E.enc(k, if b then m1 else m0);
    b' <@ A.distinguish(c);
    return b';
  }
}.

(**
  We have defined our assumptions, we can now define our
  constructive goal.

  A public key encryption scheme (with structured ciphertexts!) is a
  triple of algorithms:
**)
module type PKE = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey, m : pt): kct * dct
  proc dec(sk : skey, c : kct * dct): pt option
}.

(** A CPA adversary against a PKE is a pair of algorithms: **)
module type PKE_CPA_Adv = {
  proc choose(pk : pkey): pt * pt
  proc distinguish(c : kct * dct): bool
}.

(**
  The advantage of a CPA adversary A against a PKE E is
    `|   Pr[PKE_CPA_Exp(E, A).run(false) @ &m: res]
       - Pr[PKE_CPA_Exp(E, A).run(true) @ &m: res]  |
  where PKE_CPA_Exp is the experiment:
**)
module PKE_CPA_Exp (E : PKE) (A : PKE_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, c, b', m0, m1;

    (pk, sk) <@ E.keygen();
    (m0, m1) <@ A.choose(pk);
    c <@ E.enc(pk, if b then m1 else m0);
    b' <@ A.distinguish(c);
    return b';
  }
}.

(*
(*
  Note: instead of defining a specialized notion of PKE with
  structured ciphertexts, we could have obtained very similar
  definitions by _instantiating_ a library definition.

  However, note that the humongous variety of ways in which CPA
  security for PKEs can be expressed makes developing such a
  library a tricky proposition.
*)
require PKE.
clone PKE as KEM_Based_PKE with
  type pkey <= pkey,
  type skey <= skey,
  type plaintext <= pt,
  type ciphertext <= kct * dct.

print KEM_Based_PKE.Scheme.
*)

(** Finally, we can define our KEM/DEM composition **)
module KEMDEM (E_kem : KEM) (E_s : DEM): PKE = {
  proc keygen = E_kem.keygen

  proc enc(pk : pkey, m : pt): kct * dct = {
    var k, kc, dc;

    (k, kc) <@ E_kem.encaps(pk);
    dc <@ E_s.enc(k, m);
    return (kc, dc);
  }

  proc dec(sk : skey, c : kct * dct): pt option = {
    var kc, dc, r, k, m;

    (kc, dc) <- c;
    r <- None;
    k <@ E_kem.decaps(sk, kc);
    if (k <> None) {
      m <@ E_s.dec(oget k, dc);
      r <- Some m;
    }
    return r;
  }
}.


(**
  And we prove its security: there exist reductions B_kem_0(E_s),
  B_kem_1(E_s) and B_s(E_kem) such that ...
**)
module B_kem_0 (E_s : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, kc: kct) = {
    var m0, m1, dc, b';

    (m0, m1) <@ A.choose(pk);
    dc <@ E_s.enc(k, m0);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.

module B_kem_1 (E_s : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, kc: kct) = {
    var m0, m1, dc, b';

    (m0, m1) <@ A.choose(pk);
    dc <@ E_s.enc(k, m1);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.

module B_s (E_kem : KEM) (A : PKE_CPA_Adv) : DEM_1CPA_Adv = {
  var pk : pkey

  proc choose() = {
    var sk, m0, m1;

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    return (m0, m1);
  }

  proc distinguish(dc : dct) = {
    var k0, kc, b';

    (k0, kc) <@ E_kem.encaps(pk);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.

section.
(* for every KEM E_kem, ... *)
declare module E_kem <: KEM { -B_s }.
(* for every DEM E_s, ... *)
declare module E_s   <: DEM { -B_s, -E_kem }.
(* and for every CPA adversary against the PKE KEMDEM(E_kem, E_s), ... *)
declare module A     <: PKE_CPA_Adv { -B_s, -E_kem, -E_s }.
(*
  we have
    Adv^{CPA}_{KEMDEM(E_kem, E_s)}(A)
 <=   Adv^{CPA}_{E_kem}(B_kem_0(E_s, A))
    + Adv^{CPA}_{E_kem}(B_kem_1(E_s, A))
    + Adv^{1CPA}_{E_s}(B_s(E_kem, A))
*)

(*
  The pen and paper proof would use an intermediate game Game1, which
  is roughly the PKE CPA experiment, but where the DEM encryption is
  carried out using a random key, instead of one obtained from KEM
  encapsulation.

  It is clearly at distance Adv^{CPA}_{E_kem} from the PKE CPA
  experiment on KEMDEM with the same parameter b. (Hop1 and Hop3.)

  The distance between Game1 with b = 0 and Game1 with b = 1 is
  clearly exactly Adv^{1CPA}_{E_s}. (Hop2.)

  Defining Game1 is unnecessary for the EasyCrypt proof itself, but
  helps present it in game-based style.
*)
local module Game1 = {
  proc run(b : bool) = {
    var pk, sk, m0, m1, k0, k1, kc, dc, b';

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    (k0, kc) <@ E_kem.encaps(pk);
    k1 <$ dkey;
    dc <@ E_s.enc(k1, if b then m1 else m0);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.

local lemma EqPr_PKECPA0_KEMCPA0 &m:
    Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
  = Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res].
proof.
(* We prove the equality by proving that the procedures are
   equivalent; we do *that* by proving that their body is equivalent
*)
byequiv=> //; proc.
(* We inline the reduction to make the PKE adversary appear on the
   right *)
inline {2} 4.
wp; call (: true). (* if the adversary runs with similar views of the
                      system (state of A, inputs), then they must end
                      with similar views of the system (output) *)
(* We inline the KEM/DEM's encryption to make encapsulation and DEM
   encryption appear *)
inline {1} 3.
wp; call (: true). (* same on DEM encryption-it's abstract! treated
                      the same as an adversary in our logic *)
(* We need to align the KEM encapsulation calls and adversary runs;
   fortunately, we know they are independent. *)
swap {1} 3 -1.
swap {1} -1 -2.
(* We then have a sequence of equivalent calls *)
wp; call (: true).
(* interrupted by a one-sided random sampling-a key we do not use *)
wp; rnd {2}.
wp; call (: true).
wp; call (: true).
by auto.
qed.

local lemma EqPr_KEMCPA1_Game10 &m:
    Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res]
  = Pr[Game1.run(false) @ &m: res].
proof.
(* Once we know how to do the proof, we can automate more of it *)
byequiv=> //; proc.
inline {1} 4.
swap {1} 4 -2.
swap {1} 7 -4.
sim.
call (: true); wp.
conseq (: ={k1, k0, pk, sk, m1, m0, glob E_s, glob A}
       /\ c{1} = kc{2})=> //.
by sim.
qed.

local lemma GameHop1 &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
   - Pr[Game1.run(false) @ &m: res] |
 = `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
    - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |.
proof. by rewrite (EqPr_PKECPA0_KEMCPA0 &m) -(EqPr_KEMCPA1_Game10 &m). qed.

local lemma GameHop2 &m:
  `| Pr[Game1.run(false) @ &m: res]
   - Pr[Game1.run(true) @ &m: res] |
  = `| Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
     - Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |.
proof.
(* With enough faith, one can shortcut named lemmas *)
have ->: Pr[Game1.run(false) @ &m: res]
       = Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res].
+ byequiv=> //; proc.
  inline {2} 4.
  swap {2} 5 -2.
  swap {2} 1 2.
  inline {2} 1.
  by sim.
have -> //: Pr[Game1.run(true) @ &m: res]
          = Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res].
byequiv=> //; proc.
swap {2} 1 1.
inline {2} 4.
swap {2} 5 -3.
inline {2} 1.
by sim.
qed.

local lemma GameHop3 &m:
  `| Pr[Game1.run(true) @ &m: res]
     - Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res] |
 = `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
    - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res] |.
proof.
have ->: Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]
       = Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res].
+ byequiv=> //; proc.
  inline *.
  swap {1} 3 -1.
  swap {1} 5 -2.
  wp; call (: true).
  wp; call (: true).
  wp; call (: true).
  wp; rnd {2}; call (: true).
  by wp; call (: true).
have -> /#: Pr[Game1.run(true) @ &m: res]
          = Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res].
byequiv=> //; proc.
inline *.
swap {2} 4 -2.
swap {2} 7 -4.
sim.
wp; call (: true).
wp; rnd.
wp; call (: true).
wp; call (: true).
by wp; call (: true).
qed.

(* We can finally conclude! *)
lemma KEMDEM_PKECPA_Security &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
   - Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]|
  <= `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |
   + `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res] |
   + `| Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
      - Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |.
proof. smt(GameHop1 GameHop2 GameHop3). qed.

end section.

print KEMDEM_PKECPA_Security.
