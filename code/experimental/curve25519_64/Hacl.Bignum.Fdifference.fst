module Hacl.Bignum.Fdifference

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Modulo
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.Fdifference
open Hacl.Spec.Bignum.Modulo

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


[@"substitute"]
val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b len))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b)))
[@"substitute"]
let rec fdifference_ a b =
  C.Loops.in_place_map2 a b clen (fun x y -> y -%^ x)

assume val lemma_diff: a:int -> b:int -> p:pos ->
  Lemma ( (a - b) % p = ((a%p) - b) % p /\ (a - b) % p = (a - (b % p)) % p)
  
#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

[@"c_inline"]
val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ add_zero_pre (as_seq h b)
      /\ Hacl.Spec.Bignum.Fdifference.gte_limbs (as_seq h a) (add_zero_spec (as_seq h b)) len))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b
      /\ live h1 a /\ modifies_1 a h0 h1
      /\ add_zero_pre (as_seq h0 b)
      /\ Hacl.Spec.Bignum.Fdifference.gte_limbs (as_seq h0 a) (add_zero_spec (as_seq h0 b)) len
      /\ eval h1 a % prime = (eval h0 b - eval h0 a) % prime
      /\ as_seq h1 a == fdifference_tot (as_seq h0 a) (as_seq h0 b)
      ))
[@"c_inline"]
let fdifference a b =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create limb_zero clen in
  let h0' = ST.get() in
  blit b 0ul tmp 0ul clen;
  let h = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h b);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h tmp);
  FStar.Seq.lemma_eq_intro (as_seq h b) (as_seq h tmp);
  add_zero tmp;
  let h' = ST.get() in
  cut (eval h' tmp % prime = eval hinit b % prime);
  fdifference_ a tmp;
  let h1 = ST.get() in
  Hacl.Spec.Bignum.Fdifference.lemma_fdifference_eval (as_seq hinit a) (as_seq h' tmp);
  lemma_diff (eval h' tmp) (eval hinit a) prime;
  lemma_diff (eval hinit b) (eval hinit a) prime;
  pop_frame();
  lemma_modifies_1_trans tmp h0' h h';
  lemma_modifies_0_1' tmp h0 h0' h';
  lemma_modifies_0_1 a h0 h' h1
