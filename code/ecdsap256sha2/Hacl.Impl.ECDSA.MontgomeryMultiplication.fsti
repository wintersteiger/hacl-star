module Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Spec.P256.Lemmas
open Spec.ECDSAP256.Definition
open Spec.ECDSA
open Hacl.Impl.LowLevel
  
open Spec.P256.Jacobian


open FStar.Mul

noextract
let order = Spec.P256.order

inline_for_extraction
let prime256order_buffer: x: ilbuffer uint64 (size 4)  
  {witnessed #uint64 #(size 4) x 
  (Lib.Sequence.of_list p256_order_prime_list) /\ recallable x /\ 
  felem_seq_as_nat (Lib.Sequence.of_list (p256_order_prime_list)) == order} = 
  createL_global p256_order_prime_list


inline_for_extraction
let order_inverse_buffer: x: ilbuffer uint8 32ul {witnessed x prime_p256_order_inverse_seq /\ recallable x} = 
  createL_global prime_p256_order_inverse_list


inline_for_extraction
let order_buffer: x: ilbuffer uint8 32ul {witnessed x prime_p256_order_seq /\ recallable x} = 
  createL_global prime_p256_order_list 


val reduction_prime_2prime_with_carry : x: widefelem -> result: felem ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat h x < 2 * order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = wide_as_nat h0 x % order)  
    

val reduction_prime_2prime_with_carry2 : carry: uint64 ->  x: felem -> result: felem ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ 
      uint_v carry * pow2 256 + as_nat h x < 2 * order )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      as_nat h1 result = (uint_v carry * pow2 256 + as_nat h0 x) % order)  


val reduction_prime_2prime_order: x: felem -> result: felem -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  as_nat h1 result == as_nat h0 x % order)  


noextract
val fromDomain_: a: nat -> Tot (r: nat {r < order})

noextract
val toDomain_: a: nat -> Tot nat

val lemmaFromDomain: a: nat ->  Lemma (
  (a * modp_inv2_prime (pow2 256) order) % order == fromDomain_ a)

val lemmaToDomain: a: nat ->  Lemma (
  (a * pow2 256) % order == toDomain_ a)


val lemmaFromDomainToDomain: a: nat {a < order} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaToDomainFromDomain: a: nat {a < order} -> Lemma (fromDomain_ (toDomain_ a) == a)


val montgomery_multiplication_ecdsa_module: a: felem -> b: felem ->result: felem-> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < order /\ as_nat h b < order)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ 
      as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) order) % order /\ 
      as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % order))


val felem_add: arg1: felem -> arg2: felem -> out: felem -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < order /\ as_nat h0 arg2 < order
   )
  )
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % order))

val lemma_felem_add: a: nat -> b: nat -> Lemma ((fromDomain_ a + fromDomain_ b) % order = fromDomain_ (a + b))
