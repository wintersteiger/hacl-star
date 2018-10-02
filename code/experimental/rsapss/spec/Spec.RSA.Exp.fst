module Spec.RSA.Exp

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Spec.RSA.Lemmas
open Spec.Bignum.Basic
open Spec.Montgomery

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let mod_inv_u64 (n0:uint64) : uint64 =
  let alpha = u64 1 <<. u32 63 in
  let beta = n0 in
  let ub, vb =
    repeati 64
    (fun i (ub, vb) ->
      let u_is_odd = u64 0 -. (ub &. u64 1) in
      let beta_if_u_is_odd = beta &. u_is_odd in
      let ub = ((ub ^. beta_if_u_is_odd) >>. u32 1) +. (ub &. beta_if_u_is_odd) in

      let alpha_if_u_is_odd = alpha &. u_is_odd in
      let vb = (vb >>. u32 1) +. alpha_if_u_is_odd in
      ub, vb
    ) (u64 1, u64 0) in
  vb

val mod_exp_f:
    nBits:size_pos
  -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> bBits:size_pos
  -> b:bignum bBits
  -> a0:bignum (nBits + 1)
  -> acc0:bignum (nBits + 1)
  -> repeatable #(tuple2 (bignum (nBits + 1)) (bignum (nBits + 1))) #bBits
	       (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0)
let mod_exp_f nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) =
  let a1 = mul_mod_mont nBits rBits nInv_u64 n a a in
  assert (bn_v a1 % bn_v n == bn_v a * bn_v a / pow2 rBits % bn_v n);
  lemma_mod_exp_a2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i;
  assert (bn_v a1 % bn_v n = pow (bn_v a0) (pow2 (i + 1)) / pow (pow2 rBits) (pow2 (i + 1) - 1) % bn_v n);
  if bn_get_bit b i = 1 then begin
    let acc1 = mul_mod_mont nBits rBits nInv_u64 n a acc in
    lemma_mod_exp_f2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 acc1 i;
    (a1, acc1) end
  else begin
    let acc1 = acc in
    lemma_mod_exp_f1 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i;
    (a1, acc1) end

val mod_exp_:
    nBits:size_pos
  -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0}
  -> nInv_u64:bignum 64
  -> n:bignum nBits{bn_v n > 0}
  -> a0:bignum (nBits + 1)
  -> bBits:size_pos
  -> b:bignum bBits
  -> acc0:bignum (nBits + 1)
  -> res:bignum (nBits + 1)
    {bn_v res % bn_v n == pow (bn_v a0) (bn_v b) * bn_v acc0 / pow (pow2 rBits) (bn_v b) % bn_v n}
let mod_exp_ nBits rBits nInv_u64 n a0 bBits b acc0 =
  let a, acc =
    repeati_inductive bBits
    (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0)
    (fun i (a, acc) -> mod_exp_f nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc))
    (a0, acc0) in
  assert (bn_v acc % bn_v n =
    pow (bn_v a0) (bn_v (bn_get_bits_first b bBits)) * bn_v acc0 /
    pow (pow2 rBits) (bn_v (bn_get_bits_first b bBits)) % bn_v n);
  assert (bn_v b < pow2 bBits);
  FStar.Math.Lemmas.small_modulo_lemma_1 (bn_v b) (pow2 bBits);
  assert (bn_v (bn_get_bits_first b bBits) == bn_v b);
  acc

val mod_exp:
    #aBits:size_pos
  -> nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t}
  -> n:bignum nBits{0 < bn_v n}
  -> a:bignum aBits{aBits <= nBits}
  -> bBits:size_pos
  -> b:bignum bBits
  -> res:bignum nBits{bn_v res == pow (bn_v a) (bn_v b) % bn_v n}
let mod_exp #aBits nBits n a bBits b =
  let nLen = blocks nBits 64 in
  let rBits = 64 * (nLen + 1) in
  let r2 = bn_pow2_r_mod n (rBits * 2) in
  let n0 = bn_get_bits n 0 64 in
  let nInv_u64 = bn_from_u64 (mod_inv_u64 (bn_to_u64 n0)) in
  let a_r = to_mont nBits rBits nInv_u64 n r2 a in
  let acc_r = to_mont nBits rBits nInv_u64 n r2 (bn_const_1 #nBits) in
  let res_r = mod_exp_ nBits rBits nInv_u64 n a_r bBits b acc_r in
  lemma_mod_exp_2 (bn_v n) (bn_v a) (bn_v a_r) (bn_v b) (bn_v acc_r) (pow2 rBits) (bn_v res_r);
  let res = from_mont nBits rBits nInv_u64 n res_r in
  lemma_mod_mult_div_1 (bn_v res_r) (pow2 rBits) (bn_v n);
  lemma_mod_mult_div_1 (pow (bn_v a) (bn_v b) * pow2 rBits) (pow2 rBits) (bn_v n);
  FStar.Math.Lemmas.multiple_division_lemma (pow (bn_v a) (bn_v b)) (pow2 rBits);
  res

val rsa_blinding:
    #mBits:size_pos
  -> nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t}
  -> n:bignum nBits{1 < bn_v n}
  -> pBits:size_pos
  -> p:bignum pBits{1 < bn_v p /\ bn_v p < bn_v n}
  -> qBits:size_pos{pBits + qBits + 65 < max_size_t}
  -> q:bignum qBits{1 < bn_v q /\ bn_v q < bn_v n /\ bn_v n == bn_v p * bn_v q}
  -> m:bignum mBits{mBits <= nBits /\ bn_v m < bn_v n}
  -> dBits:size_pos{dBits < pBits + qBits + 64}
  -> d:bignum dBits{0 < bn_v d /\ bn_v d < bn_v n}
  -> rBlind:bignum 64
  -> s:bignum nBits{bn_v s == pow (bn_v m) (bn_v d) % bn_v n}
let rsa_blinding #mBits nBits n pBits p qBits q m dBits d rBlind =
  let bn_1 = bn_const_1 #1 in
  let p1 = bn_sub p bn_1 in
  let q1 = bn_sub q bn_1 in
  let phi_n = bn_mul p1 q1 in
  let d1 = bn_mul phi_n rBlind in
  let d2 = bn_add_carry d1 d in
  assert (bn_v d2 == bn_v d + bn_v rBlind * bn_v phi_n);
  let s = mod_exp nBits n m (pBits + qBits + 65) d2 in
  lemma_exp_blinding_bn #nBits #pBits #qBits #dBits #mBits n phi_n p q d m rBlind;
  s
