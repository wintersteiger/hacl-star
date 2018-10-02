module Spec.Karatsuba.Lemmas

open FStar.Mul
open Lib.IntTypes
open Spec.Bignum.Basic

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let size_pos = x:size_nat{x > 0}

val abs:x:int -> y:nat{y == (if x >= 0 then x else -x)}
let abs x = if x >= 0 then x else -x

type sign =
  | Positive : sign
  | Negative : sign

val lemma_add_sign:
    c0:nat -> c1:nat -> c2:nat
  -> a0:nat -> a1:nat -> a2:nat
  -> b0:nat -> b1:nat -> b2:nat
  -> sa2:sign -> sb2:sign
  -> Lemma
    (requires
      c0 == a0 * b0 /\ c1 == a1 * b1 /\ c2 == a2 * b2 /\
      a2 == abs (a0 - a1) /\ b2 == abs (b0 - b1) /\
      sa2 = (if a0 >= a1 then Positive else Negative) /\
      sb2 = (if b0 >= b1 then Positive else Negative))
  (ensures
    (if sa2 = sb2 then (c0 + c1 - c2 == a1 * b0 + a0 * b1)
    else (c0 + c1 + c2 == a1 * b0 + a0 * b1)))
let lemma_add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 = ()

val lemma_add_sign1:
     a0Bits:size_pos
  -> a1Bits:size_pos{a0Bits + a1Bits + 1 < max_size_t}
  -> a0:bignum a0Bits
  -> a1:bignum a1Bits
  -> b0:bignum a0Bits
  -> b1:bignum a1Bits
  -> Lemma (bn_v a1 * bn_v b0 + bn_v a0 * bn_v b1 < pow2 (a0Bits + a1Bits + 1))
let lemma_add_sign1 a0Bits a1Bits a0 a1 b0 b1 =
  let res = bn_v a1 * bn_v b0 + bn_v a0 * bn_v b1 in
  assume (res < pow2 a1Bits * pow2 a0Bits + pow2 a0Bits * pow2 a1Bits);
  FStar.Math.Lemmas.pow2_plus a1Bits a0Bits;
  FStar.Math.Lemmas.pow2_double_sum (a0Bits + a1Bits)

val lemma_distributivity_mult:
  a:nat -> b:nat -> c:nat -> d:nat
  -> Lemma ((a + b) * (c + d) = a * c + a * d + b * c + b * d)
let lemma_distributivity_mult a b c d = ()

val lemma_karatsuba_mult:
     aBits:size_pos
  -> a0Bits:size_pos
  -> a1Bits:size_pos{a0Bits + a1Bits == aBits}
  -> a:nat{a < pow2 aBits}
  -> a0:nat{a0 < pow2 a0Bits}
  -> a1:nat{a1 < pow2 a1Bits}
  -> b:nat{b < pow2 aBits}
  -> b0:nat{b0 < pow2 a0Bits}
  -> b1:nat{b1 < pow2 a1Bits}
  -> Lemma
    (requires
      a == a1 * pow2 a0Bits + a0 /\
      b == b1 * pow2 a0Bits + b0)
    (ensures
      a * b == a1 * b1 * pow2 (a0Bits + a0Bits) + (a0 * b1 + a1 * b0) * pow2 a0Bits + a0 * b0)
let lemma_karatsuba_mult aBits a0Bits a1Bits a a0 a1 b b0 b1 =
  assert (a * b == (a1 * pow2 a0Bits + a0) * (b1 * pow2 a0Bits + b0));
  lemma_distributivity_mult (a1 * pow2 a0Bits) a0 (b1 * pow2 a0Bits) b0;
  assert (a * b == a0 * b0 + a1 * b1 * pow2 a0Bits * pow2 a0Bits + a0 * b1 * pow2 a0Bits + a1 * b0 * pow2 a0Bits);
  FStar.Math.Lemmas.pow2_plus a0Bits a0Bits

val lemma_mul_pow2:
    aBits:size_pos
  -> a:bignum aBits
  -> b:bignum aBits
  -> Lemma
    (bn_v a * bn_v b < pow2 (aBits + aBits))
let lemma_mul_pow2 aBits a b =
  assume (bn_v a * bn_v b < pow2 aBits * pow2 aBits);
  FStar.Math.Lemmas.pow2_plus aBits aBits

val lemma_get_bits:
    aBits:size_pos
  -> a0Bits:size_pos{a0Bits % 64 == 0 /\ a0Bits < aBits}
  -> a:bignum aBits
  -> a0:bignum a0Bits
  -> a1:bignum (aBits - a0Bits)
  -> Lemma
    (requires
      bn_v a0 == bn_v (bn_get_bits a 0 a0Bits) /\
      bn_v a1 == bn_v (bn_get_bits a a0Bits aBits))
    (ensures bn_v a == bn_v a0 + bn_v a1 * pow2 a0Bits)
let lemma_get_bits aBits a0Bits a a0 a1 =
  assert (bn_v a0 == bn_v a % pow2 a0Bits);
  assert (bn_v a1 == bn_v a / pow2 a0Bits % pow2 (aBits - a0Bits));
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v a) a0Bits aBits;
  assert (bn_v a1 == bn_v a % pow2 aBits / pow2 a0Bits);
  FStar.Math.Lemmas.small_modulo_lemma_1 (bn_v a) (pow2 aBits);
  assert (bn_v a1 == bn_v a / pow2 a0Bits);
  FStar.Math.Lemmas.euclidean_division_definition (bn_v a) (pow2 a0Bits)
