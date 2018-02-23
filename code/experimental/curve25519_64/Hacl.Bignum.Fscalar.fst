module Hacl.Bignum.Fscalar

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Bignum.Fproduct
open Hacl.Bignum.Modulo
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.Fscalar
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Modulo

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"


[@"substitute"]
val fscalar_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == fscalar_spec (as_seq h0 input) s))
[@"substitute"]
let fscalar_ output b s =
  C.Loops.map output b clen (fun x -> Hacl.Bignum.Wide.mul_wide x s)

[@"c_inline"]
val fscalar:
  a:felem ->
  b:felem{disjoint a b} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h b /\ live h a
      /\ carry_wide_pre (fscalar_spec (as_seq h b) s) 0
      /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec (as_seq h b) s))
      /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec (as_seq h b) s))) ))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ modifies_1 a h0 h1 /\ live h1 a
      /\ eval h1 a % prime = (eval h0 b * v s) % prime
      /\ carry_wide_pre (fscalar_spec (as_seq h0 b) s) 0
      /\ carry_top_wide_pre (carry_wide_spec (fscalar_spec (as_seq h0 b) s))
      /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fscalar_spec (as_seq h0 b) s)))
      /\ as_seq h1 a == fscalar_tot (as_seq h0 b) s
    ))

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0"
[@"c_inline"]
let fscalar output b s = Hacl.Bignum.fscalar output b s
