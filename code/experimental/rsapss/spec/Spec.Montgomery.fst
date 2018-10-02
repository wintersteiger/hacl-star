module Spec.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Montgomery.Lemmas
open Spec.Bignum.Basic

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val mont_pred:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits
  -> i:size_nat{i <= rBits / 64}
  -> res:bignum (nBits + 1 + rBits)
  -> Tot Type0
let mont_pred #nBits #cBits rBits nInv_u64 n c i res =
  bn_v res % bn_v n == bn_v c % bn_v n /\
  bn_v res <= bn_v c + (pow2 (64 * i) - 1) * bn_v n

val mont_reduction_f:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits + 1 + rBits < max_size_t}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits{nBits < rBits /\ cBits < nBits + rBits}
  -> repeatable #(bignum (nBits + 1 + rBits)) #(rBits / 64) (mont_pred #nBits #cBits rBits nInv_u64 n c)
let mont_reduction_f #nBits #cBits rBits nInv_u64 n c i res =
  let res_i = bn_get_bits res (i * 64) ((i + 1) * 64) in
  let qi = bn_get_bits (bn_mul nInv_u64 res_i) 0 64 in
  assert (bn_v res + bn_v n * pow2 (64 * i) * bn_v qi <=
    bn_v c + (pow2 (64 * i) - 1) * bn_v n + bn_v n * pow2 (64 * i) * bn_v qi);
  lemma_mont_reduction_fi #nBits #cBits rBits qi n c i res;
  lemma_mont_reduction_f #nBits #cBits rBits n c i;
  assert (bn_v res + bn_v n * pow2 (64 * i) * bn_v qi < pow2 (nBits + 1 + rBits));
  let res1 = bn_lshift_mul_add n (64 * i) qi res in
  assert (bn_v res1 % bn_v n == (bn_v res + bn_v n * pow2 (64 * i) * bn_v qi) % bn_v n);
  assume (bn_v n * pow2 (64 * i) * bn_v qi == pow2 (64 * i) * bn_v qi * bn_v n);
  FStar.Math.Lemmas.lemma_mod_plus (bn_v res) (pow2 (64 * i) * bn_v qi) (bn_v n); // res1 % n == res % n
  res1

val mont_reduction_:
     #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits{cBits < nBits + rBits}
  -> res:bignum (nBits + 1 + rBits)
    {bn_v res % bn_v n = bn_v c % bn_v n /\
     bn_v res <= bn_v c + (pow2 rBits - 1) * bn_v n}
let mont_reduction_ #nBits #cBits rBits nInv_u64 n c =
  FStar.Math.Lemmas.pow2_lt_compat (nBits + 1 + rBits) cBits;
  let tmp = bn_cast_gt (nBits + 1 + rBits) c in
  let rLen = rBits / 64 in
  repeati_inductive rLen
  (mont_pred #nBits #cBits rBits nInv_u64 n c)
  (fun i res ->
    mont_reduction_f rBits nInv_u64 n c i res) tmp

val mont_reduction:
    #nBits:size_pos
  -> #cBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> c:bignum cBits{cBits < nBits + rBits}
  -> res:bignum (nBits + 1){bn_v res % bn_v n == bn_v c / pow2 rBits % bn_v n}
let mont_reduction #nBits #cBits rBits nInv_u64 n c =
  let tmp = mont_reduction_ rBits nInv_u64 n c in
  assert (bn_v tmp % bn_v n = bn_v c % bn_v n && bn_v tmp <= bn_v c + (pow2 rBits - 1) * bn_v n);
  lemma_mont_reduction #nBits #cBits rBits n c;
  let res = bn_rshift tmp rBits in
  assert (bn_v res % bn_v n == bn_v tmp / pow2 rBits % bn_v n);
  lemma_mod_mult_div_1 (bn_v tmp) (pow2 rBits) (bn_v n);
  assert (bn_v res % bn_v n == (bn_v c % bn_v n) / pow2 rBits % bn_v n);
  lemma_mod_mult_div_1 (bn_v c) (pow2 rBits) (bn_v n);
  res

val mul_mod_mont:
  nBits:size_pos
  -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> a:bignum (nBits + 1)
  -> b:bignum (nBits + 1)
  -> res:bignum (nBits + 1){bn_v res % bn_v n == bn_v a * bn_v b / pow2 rBits % bn_v n}
let mul_mod_mont nBits rBits nInv_u64 n a b =
  //let c = bn_mul a b in
  let c = Spec.Karatsuba.karatsuba (nBits+1) a b in
  assert (bn_v c < pow2 (nBits + nBits + 2));
  mont_reduction rBits nInv_u64 n c

val to_mont:
    #aBits:size_pos
  -> nBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> r2:bignum nBits{bn_v r2 == pow2 (2 * rBits) % bn_v n}
  -> a:bignum aBits{aBits <= nBits}
  -> res:bignum (nBits + 1){bn_v res % bn_v n == bn_v a * pow2 rBits % bn_v n}
let to_mont #aBits nBits rBits nInv_u64 n r2 a =
  let c = bn_mul a r2 in
  assert (bn_v c < pow2 (aBits + nBits));
  let res = mont_reduction rBits nInv_u64 n c in
  assert (bn_v res % bn_v n == bn_v c / pow2 rBits % bn_v n);
  lemma_mod_mult_div_1 (bn_v c) (pow2 rBits) (bn_v n);
  assert (bn_v c % bn_v n == bn_v a * bn_v r2 % bn_v n);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (bn_v r2) (bn_v a) (bn_v n);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (pow2 (2 * rBits)) (bn_v a) (bn_v n);
  lemma_mod_mult_div_1 (bn_v a * pow2 (2 * rBits)) (pow2 rBits) (bn_v n);
  assert (bn_v res % bn_v n == bn_v a * pow2 (2 * rBits) / pow2 rBits % bn_v n);
  FStar.Math.Lemmas.pow2_multiplication_division_lemma_1 (bn_v a) rBits (2 * rBits);
  assert (bn_v res % bn_v n == bn_v a * pow2 rBits % bn_v n);
  res

val from_mont:
     nBits:size_pos
  -> rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> a_r:bignum (nBits + 1)
  -> res:bignum nBits{bn_v res == bn_v a_r / pow2 rBits % bn_v n}
let from_mont nBits rBits nInv_u64 n a_r =
  let tmp = mont_reduction_ rBits nInv_u64 n a_r in
  assert (bn_v tmp % bn_v n = bn_v a_r % bn_v n /\ bn_v tmp < bn_v a_r + pow2 rBits * bn_v n);
  let res = bn_rshift tmp rBits in
  lemma_mod_mult_div_1 (bn_v tmp) (pow2 rBits) (bn_v n);
  lemma_mod_mult_div_1 (bn_v a_r) (pow2 rBits) (bn_v n);
  assume (bn_v res < bn_v n);
  let res = bn_cast_le nBits res in
  FStar.Math.Lemmas.small_modulo_lemma_1 (bn_v res) (bn_v n);
  res
