module Spec.Karatsuba

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.RSA.Lemmas
open Spec.Bignum.Basic
open Spec.Karatsuba.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val abs_sub:
     #aBits:size_pos
  -> #bBits:size_pos{bBits <= aBits}
  -> a:bignum aBits
  -> b:bignum bBits
  -> Pure (tuple2 sign (bignum aBits))
    (requires True)
    (ensures (fun (s, res) ->
      bn_v res = abs (bn_v a - bn_v b) /\
      s = (if bn_v a >= bn_v b then Positive else Negative)))
let abs_sub #aBits #bBits a b =
  if bn_is_less a b then begin
    let res = bn_sub b a in
    FStar.Math.Lemmas.pow2_le_compat aBits bBits;
    let res = bn_cast_gt aBits res in
    (Negative, res) end
  else
    (Positive, bn_sub a b)

val add_sign:
     #a0Bits:size_pos{a0Bits + a0Bits + 1 < max_size_t}
  -> #a1Bits:size_pos{a1Bits + a1Bits < max_size_t /\ a1Bits <= a0Bits}
  -> c0:bignum (a0Bits + a0Bits)
  -> c1:bignum (a1Bits + a1Bits)
  -> c2:bignum (a0Bits + a0Bits)
  -> a0:bignum a0Bits
  -> a1:bignum a1Bits
  -> a2:bignum a0Bits
  -> b0:bignum a0Bits
  -> b1:bignum a1Bits
  -> b2:bignum a0Bits
  -> sa2:sign
  -> sb2:sign
  -> Pure (bignum (a0Bits + a0Bits + 1))
    (requires
       bn_v c0 == bn_v a0 * bn_v b0 /\
       bn_v c1 == bn_v a1 * bn_v b1 /\
       bn_v c2 == bn_v a2 * bn_v b2 /\
       bn_v a2 == abs (bn_v a0 - bn_v a1) /\
       bn_v b2 == abs (bn_v b0 - bn_v b1) /\
       sa2 = (if bn_v a0 >= bn_v a1 then Positive else Negative) /\
       sb2 = (if bn_v b0 >= bn_v b1 then Positive else Negative))
    (ensures fun res ->
      bn_v res == bn_v (bn_add_carry (bn_mul a1 b0) (bn_mul a0 b1)))
let add_sign #a0Bits #a1Bits c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 =
  lemma_add_sign (bn_v c0) (bn_v c1) (bn_v c2) (bn_v a0) (bn_v a1)
    (bn_v a2) (bn_v b0) (bn_v b1) (bn_v b2) sa2 sb2;
  let c01 = bn_add_carry c0 c1 in
  if sa2 = sb2 then
    bn_sub c01 c2
  else begin
    assert (bn_v c0 + bn_v c1 + bn_v c2 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    lemma_add_sign1 a0Bits a1Bits a0 a1 b0 b1;
    FStar.Math.Lemmas.pow2_le_compat (a0Bits + a0Bits + 1) (a0Bits + a1Bits + 1);
    assert (bn_v c0 + bn_v c1 + bn_v c2 < pow2 (a0Bits + a0Bits + 1));
    bn_add c01 c2
  end

val karatsuba_f:
     #aBits:size_pos{aBits + aBits < max_size_t}
  -> #a0Bits:size_pos
  -> #a1Bits:size_pos{a0Bits + a1Bits = aBits /\ a1Bits <= a0Bits}
  -> c0:bignum (a0Bits + a0Bits)
  -> c1:bignum (a1Bits + a1Bits)
  -> tmp:bignum (a0Bits + a0Bits + 1){bn_v tmp < pow2 (a0Bits + a1Bits + 1)}
  -> Pure (bignum (aBits + aBits))
    (requires
      bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits < pow2 (aBits + aBits))
    (ensures
      fun res -> bn_v res == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits)
let karatsuba_f #aBits #a0Bits #a1Bits c0 c1 tmp =
  let c = bn_const_0 #(aBits + aBits) in
  FStar.Math.Lemmas.pow2_lt_compat (aBits + aBits) (a0Bits + a0Bits);
  let res0 = bn_add c c0 in
  assert (bn_v res0 == bn_v c + bn_v c0);
  FStar.Math.Lemmas.pow2_lt_compat (aBits + aBits) (a1Bits + a1Bits);
  let res1 = bn_lshift_add c1 (a0Bits + a0Bits) res0 in
  assert (bn_v res1 == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits));
  let tmp = bn_cast_le (a0Bits + a1Bits + 1) tmp in
  FStar.Math.Lemmas.pow2_lt_compat (aBits + aBits) (a0Bits + a1Bits + 1);
  let res2 = bn_lshift_add tmp a0Bits res1 in
  assert (bn_v res2 == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits);
  res2

val karatsuba:
     aBits:size_pos{aBits + aBits < max_size_t}
  -> a:bignum aBits
  -> b:bignum aBits
  -> Tot (res:bignum (aBits + aBits){bn_v res == bn_v a * bn_v b}) (decreases aBits)
let rec karatsuba aBits a b =
  if aBits < 10 * 64 then bn_mul a b
  else begin
    let len = blocks aBits 64 in
    let a0Bits = 64 * blocks len 2 in
    let a1Bits = aBits - a0Bits in
    assert (a1Bits <= a0Bits);

    let a0 = bn_get_bits a 0 a0Bits in
    let a1 = bn_get_bits a a0Bits aBits in
    lemma_get_bits aBits a0Bits a a0 a1;

    let b0 = bn_get_bits b 0 a0Bits in
    let b1 = bn_get_bits b a0Bits aBits in
    lemma_get_bits aBits a0Bits b b0 b1;

    let sa2, a2 = abs_sub a0 a1 in
    let sb2, b2 = abs_sub b0 b1 in

    let c0 = karatsuba a0Bits a0 b0 in
    assert (bn_v c0 == bn_v a0 * bn_v b0);
    let c1 = karatsuba a1Bits a1 b1 in
    assert (bn_v c1 == bn_v a1 * bn_v b1);
    let c2 = karatsuba a0Bits a2 b2 in
    assert (bn_v c2 == bn_v a2 * bn_v b2);

    let tmp = add_sign #a0Bits #a1Bits c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 in
    assert (bn_v tmp == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    lemma_karatsuba_mult aBits a0Bits a1Bits (bn_v a) (bn_v a0) (bn_v a1) (bn_v b) (bn_v b0) (bn_v b1);
    lemma_mul_pow2 aBits a b;
    let res = karatsuba_f #aBits #a0Bits #a1Bits c0 c1 tmp in
    assert (bn_v res == bn_v a * bn_v b);
    res
  end
