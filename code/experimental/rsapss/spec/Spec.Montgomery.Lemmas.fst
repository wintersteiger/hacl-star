module Spec.Montgomery.Lemmas

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Spec.Bignum.Basic

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

// (1 / d) % n is an inverse element of d
val lemma_mod_mult_div_1:a:nat -> d:pos -> n:pos
  -> Lemma (a / d % n == (a % n) / d % n)
let lemma_mod_mult_div_1 a d n = admit()

val lemma_mont_reduction_f:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t}
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits{cBits < nBits + rBits}
  -> i:size_nat{64 * (i + 1) <= rBits}
  -> Lemma
    (requires True)
    (ensures
      bn_v c + (pow2 (64 * (i + 1)) - 1) * bn_v n < pow2 (nBits + 1 + rBits))
let lemma_mont_reduction_f #nBits #cBits rBits n c i =
  pow2_le_compat rBits (64 * (i + 1));
  assert (bn_v c + (pow2 (64 * (i + 1)) - 1) * bn_v n < pow2 cBits + pow2 rBits * pow2 nBits);
  pow2_plus rBits nBits;
  pow2_lt_compat (nBits + rBits) cBits;
  assert (bn_v c + (pow2 (64 * (i + 1)) - 1) * bn_v n < pow2 (nBits + rBits) + pow2 (nBits + rBits));
  pow2_double_sum (nBits + rBits)

val lemma_mont_reduction:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits+1+rBits < max_size_t}
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits{cBits < nBits + rBits}
  -> Lemma
    (requires True)
    (ensures  bn_v c + (pow2 rBits - 1) * bn_v n < pow2 (nBits + 1 + rBits))
let lemma_mont_reduction #nBits #cBits rBits n c =
  assert (bn_v c + (pow2 rBits - 1) * bn_v n < pow2 cBits + pow2 rBits * pow2 nBits);
  pow2_plus rBits nBits;
  pow2_lt_compat (nBits + rBits) cBits;
  assert (bn_v c + (pow2 rBits - 1) * bn_v n < pow2 (nBits + rBits) + pow2 (nBits + rBits));
  pow2_double_sum (nBits + rBits)

val lemma_mont_reduction_fi:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t}
  -> qi:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits
  -> i:size_nat{i <= rBits / 64}
  -> res:bignum (nBits + 1 + rBits)
  -> Lemma
    (requires
      bn_v res + bn_v n * pow2 (64 * i) * bn_v qi <=
      bn_v c + (pow2 (64 * i) - 1) * bn_v n + bn_v n * pow2 (64 * i) * bn_v qi)
    (ensures
      bn_v res + bn_v n * pow2 (64 * i) * bn_v qi <=
      bn_v c + (pow2 (64 * (i + 1)) - 1) * bn_v n)
let lemma_mont_reduction_fi #nBits #cBits rBits qi n c i res =
  let res1 = bn_v res + bn_v n * pow2 (64 * i) * bn_v qi in
  assert (res1 <= bn_v c + (pow2 (64 * i) - 1) * bn_v n + bn_v n * pow2 (64 * i) * bn_v qi); //from ind hypo
  assert (bn_v qi < pow2 64);
  FStar.Math.Lemmas.lemma_mult_le_right (bn_v n * pow2 (64 * i)) (bn_v qi) (pow2 64 - 1);
  assert (res1 <= bn_v c + (pow2 (64 * i) - 1) * bn_v n + bn_v n * pow2 (64 * i) * (pow2 64 - 1));
  assert (res1 <= bn_v c + pow2 (64 * i) * bn_v n - bn_v n + bn_v n * pow2 (64 * i) * (pow2 64 - 1));
  assert (res1 <= bn_v c + pow2 (64 * i) * bn_v n - bn_v n + bn_v n * pow2 (64 * i) * pow2 64 - bn_v n * pow2 (64 * i));
  assert (res1 <= bn_v c - bn_v n + bn_v n * pow2 (64 * i) * pow2 64);
  assert (res1 <= bn_v c + (pow2 (64 * i) * pow2 64 - 1) * bn_v n);
  pow2_plus (64 * i) 64;
  assert (res1 <= bn_v c + (pow2 (64 * (i + 1)) - 1) * bn_v n)
