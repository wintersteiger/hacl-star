module Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.P256.Lemmas
open Spec.P256.Definitions

open Lib.IntTypes

open Spec.P256.Field
open Spec.P256.Jacobian

noextract
val fromDomain_: a: elem -> Tot elem

noextract
val fromDomainPoint: a: pointJ -> Tot (r: pointJ
  {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z
  }
)

noextract
val toDomain_: a: elem -> Tot elem

val lemmaFromDomain: a: elem -> Lemma (fromDomain_ a == a * modp_inv2 (pow2 256) % prime)

val lemmaToDomain: a: elem -> Lemma (toDomain_ a == a * (pow2 256) % prime)

val lemmaToDomainAndBackIsTheSame: a: elem -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: elem -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaFromDomainToDomainModuloPrime: a: elem -> Lemma (a % prime == fromDomain_ (toDomain_ a))

val inDomain_mod_is_not_mod: a: elem -> Lemma (toDomain_ a == toDomain_ (a % prime))

val multiplicationInDomainNat: #k: elem -> #l: elem ->
  a: nat {a == toDomain_ k /\ a < prime} -> 
  b: nat {b == toDomain_ l /\ b < prime} ->
  Lemma (
    let multResult = a * b * modp_inv2_prime (pow2 256) prime % prime in 
    multResult == toDomain_ (k *% l))

val additionInDomain: a: elem -> b: elem -> 
  Lemma (a +% b == toDomain_ (fromDomain_ a +% fromDomain_ b))

val substractionInDomain: a: elem -> b: elem -> 
  Lemma (a -% b == toDomain_ (fromDomain_ a -% fromDomain_ b))
