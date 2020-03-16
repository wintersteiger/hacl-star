module Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.P256.Lemmas
open Spec.P256.Definitions

open Lib.IntTypes

open Spec.P256.Field

noextract
val fromDomain_: a: int -> Tot (a: nat {a < prime})

noextract
val fromDomainPoint: a: tuple3 nat nat nat -> Tot (r: tuple3 nat nat nat 
  {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z
  }
)

noextract
val toDomain_: a: int -> Tot nat

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime)

val lemmaToDomain: a: int -> Lemma (toDomain_(a) == a * (pow2 256) % prime)

val lemmaToDomainAndBackIsTheSame: a: nat {a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaFromDomainToDomainModuloPrime: a: int -> Lemma (a % prime == fromDomain_(toDomain_ a))

val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime))

val multiplicationInDomainNat: #k: nat -> #l: nat ->
  a: nat {a == toDomain_ k /\ a < prime} -> 
  b: nat {b == toDomain_ l /\ b < prime} ->
  Lemma (
    let multResult = a * b * modp_inv2_prime (pow2 256) prime % prime in 
    multResult == toDomain_ (k * l))

val additionInDomain: a: nat {a < prime} -> b: nat {b < prime} -> Lemma 
  ((a + b) % prime == toDomain_ (fromDomain_ a + fromDomain_ b))

val substractionInDomain: a: nat {a < prime} -> b: nat { b < prime} -> Lemma 
  ((a - b) % prime == toDomain_ (fromDomain_ a - fromDomain_ b))
