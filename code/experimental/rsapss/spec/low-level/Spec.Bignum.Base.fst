module Spec.Bignum.Base

open FStar.Mul

open Lib.IntTypes

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val eq_u8:a:uint8 -> b:uint8 -> Tot bool
let eq_u8 a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

val lt_u64:a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

val le_u64:a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

let addcarry_u64 a b c =
  let c = to_u64 c in
  let t1 = a +. c in
  let c = if lt_u64 t1 c then u64 1 else u64 0 in
  let res = t1 +. b in
  let c = if lt_u64 res t1 then c +. u64 1 else c in
  let c = to_u8 c in
  c, res

let subborrow_u64 a b c =
  let res = a -. b -. to_u64 c in
  let c =
    if eq_u8 c (u8 1) then
      (if le_u64 a b then u8 1 else u8 0)
    else
      (if lt_u64 a b then u8 1 else u8 0) in
  c, res

val lemma_mul_carry_add_64:
  a:uint64 -> b:uint64 -> c:uint64 -> d:uint64
  -> Lemma (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128)
let lemma_mul_carry_add_64 a b c d =
  let n = pow2 64 in
  assert (uint_v a <= n - 1 /\ uint_v b <= n - 1 /\ uint_v c <= n - 1 /\ uint_v d <= n - 1);
  assert (uint_v a * uint_v b + uint_v c + uint_v d <= (n - 1) * (n - 1) + (n - 1) + (n - 1));
  assert ((n - 1) * (n - 1) + (n - 1) + (n - 1) == n * n - 1);
  FStar.Math.Lemmas.pow2_plus 64 64

#set-options "--z3rlimit 100"

let mul_carry_add_u64 a b c d =
  lemma_mul_carry_add_64 a b c d;
  assert (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128);
  let res = mul_wide a b +. to_u128 #U64 c +. to_u128 #U64 d in
  let r = to_u64 res in
  let c' = to_u64 (res >>. u32 64) in
  c', r
