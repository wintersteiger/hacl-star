module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Lib.IntTypes

open Spec.P256.Field

#set-options "--z3rlimit 300"


let fromDomain_ a = (a * modp_inv2 (pow2 256)) % prime


let fromDomainPoint a = 
  let x, y, z = a in 
  fromDomain_ x, fromDomain_ y, fromDomain_ z


let toDomain_ a = (a * pow2 256) % prime

let lemmaFromDomain a = ()


let lemmaToDomain a = ()


let lemmaToDomainAndBackIsTheSame a = 
  let to = toDomain_ a in 
  lemmaToDomain a;
  let from = fromDomain_ to in 
  lemmaFromDomain to;
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_lemma a prime


let lemmaFromDomainToDomain a = 
  let from = fromDomain_ a in 
  lemmaFromDomain a;
  let to = toDomain_ from in 
  lemmaToDomain from;
  lemma_mod_mul_distr_l (a * modp_inv2 (pow2 256)) (pow2 256) prime;
  assert_norm (modp_inv2 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 (pow2 256)) (pow2 256) prime;
  modulo_lemma a prime


let lemmaFromDomainToDomainModuloPrime a = 
  lemma_mod_mul_distr_l (a*pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime


let inDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (pow2 256) prime


let multiplicationInDomainNat #k #l a b = 
  modulo_distributivity_mult2 (k * pow2 256) (l * pow2 256) (modp_inv2_prime (pow2 256) prime) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_mul_ass3 k (pow2 256) l


let additionInDomain a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  modulo_distributivity (k * pow2 256) (l * pow2 256) prime


let substractionInDomain a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  lemma_mod_sub_distr a (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime

