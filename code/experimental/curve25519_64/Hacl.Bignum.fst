module Hacl.Bignum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Endianness

module U8 = FStar.UInt8
module U32 = FStar.UInt32

type uint8_p = buffer Hacl.UInt8.t

[@"c_inline"]
assume val addcarry_u64:
  carry:U8.t -> input1:limb -> input2:limb ->
  output:limb -> Stack U8.t
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))

[@"c_inline"]
assume val subborrow_u64: 
  carry:U8.t -> input1:limb -> input2:limb ->
  output:limb -> Stack U8.t
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))

[@"c_inline"]
assume val mulx_u64:
  input1:limb -> input2:limb -> bh:limb ->
  Stack limb
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))

val reduce_top:
  output:felem -> top:limb -> Stack U8.t
  (requires (fun h -> live h output))
  (ensures (fun h0 _ h1 -> True))
[@"substitute" ]
let reduce_top output top =
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let output2 = output.(2ul) in
  let output3 = output.(3ul) in
  
  let c = 0uy in
  let c = addcarry_u64 c output0 top output0 in
  let c = addcarry_u64 c output1 (uint64_to_limb 0uL) output1 in
  let c = addcarry_u64 c output2 (uint64_to_limb 0uL) output2 in
  let c = addcarry_u64 c output3 (uint64_to_limb 0uL) output3 in
  c

val fcontract:
  output:uint8_p{length output = 32} ->
  input:felem{disjoint output input} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> True))

#reset-options "--z3rlimit 50 --max_fuel 0"
[@"substitute" ]
let fcontract output input =
  let top = input.(3ul) in
  input.(3ul) <- top &^ (uint64_to_limb 0x7fffffffffffffffuL);
  let top = 19uL *^ (top >>^ 63ul) in
  let _ = reduce_top input top in
  
  (* we can't compare the bignum with the modulo p *)
  let output0 = Buffer.sub output 0ul  8ul in
  let output1 = Buffer.sub output 8ul  8ul in
  let output2 = Buffer.sub output 16ul 8ul in
  let output3 = Buffer.sub output 24ul 8ul in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in  
  hstore64_le output0 input0;
  hstore64_le output1 input1;
  hstore64_le output2 input2;
  hstore64_le output3 input3

val fexpand:
  output:felem ->
  input:uint8_p{length input = 32} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> True))
[@"substitute" ]
let fexpand output input =
  let input0 = Buffer.sub input 0ul 8ul in
  let input1 = Buffer.sub input 8ul 8ul in
  let input2 = Buffer.sub input 16ul 8ul in
  let input3 = Buffer.sub input 24ul 8ul in
  output.(0ul) <- hload64_le input0;
  output.(1ul) <- hload64_le input1;
  output.(2ul) <- hload64_le input2;
  output.(3ul) <- (hload64_le input3) &^ (uint64_to_limb 0x7fffffffffffffffuL)

val fsum:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> True))
[@"substitute" ]
let fsum a b =
  let a0 = a.(0ul) in let a1 = a.(1ul) in
  let a2 = a.(2ul) in let a3 = a.(3ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in
  let b2 = b.(2ul) in let b3 = b.(3ul) in
  
  let c = 0uy in
  let c = addcarry_u64 c a0 b0 a0 in
  let c = addcarry_u64 c a1 b1 a1 in
  let c = addcarry_u64 c a2 b2 a2 in
  let c = addcarry_u64 c a3 b3 a3 in
  
  let top = 38uL *^ (FStar.Int.Cast.uint8_to_uint64 c) in
  let _ = reduce_top a top in ()

val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> True))
[@"substitute" ]
let fdifference a b =
  push_frame();
  let a0 = a.(0ul) in let a1 = a.(1ul) in
  let a2 = a.(2ul) in let a3 = a.(3ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in
  let b2 = b.(2ul) in let b3 = b.(3ul) in
  
  let tmp = create 0uL 5ul in
  let tmp0 = tmp.(0ul) in let tmp1 = tmp.(1ul) in
  let tmp2 = tmp.(2ul) in let tmp3 = tmp.(3ul) in
  let tmp4 = tmp.(4ul) in
  
  let c = 0uy in
  let c = addcarry_u64 c b0 (uint64_to_limb 0xffffffffffffffdauL) tmp0 in
  let c = addcarry_u64 c b1 (uint64_to_limb 0xffffffffffffffffuL) tmp1 in
  let c = addcarry_u64 c b2 (uint64_to_limb 0xffffffffffffffffuL) tmp2 in
  let c = addcarry_u64 c b3 (uint64_to_limb 0xffffffffffffffffuL) tmp3 in
  let c = addcarry_u64 c 0uL 0uL tmp4 in

  let c = 0uy in
  let c = subborrow_u64 c tmp0 a0 tmp0 in
  let c = subborrow_u64 c tmp1 a1 tmp1 in 
  let c = subborrow_u64 c tmp2 a2 tmp2 in
  let c = subborrow_u64 c tmp3 a3 tmp3 in
  let c = subborrow_u64 c tmp4 0uL tmp4 in

  let top = 38uL *^ tmp4 in
  let c = reduce_top tmp top in
  
  let top = 38uL *^ (FStar.Int.Cast.uint8_to_uint64 c) in
  let _ = reduce_top tmp top in

  a.(0ul) <- tmp0;
  a.(1ul) <- tmp1;
  a.(2ul) <- tmp2;
  a.(3ul) <- tmp3;
  pop_frame()

val fscalar:
  a:felem ->
  b:felem{disjoint a b} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> True))
[@"substitute"]
let fscalar a b s =
  let b0 = b.(0ul) in let b1 = b.(1ul) in
  let b2 = b.(2ul) in let b3 = b.(3ul) in

  let h0 = 0uL in let h1 = 0uL in
  let h2 = 0uL in let h3 = 0uL in
  let h4 = 0uL in let l4 = 0uL in
  
  let l0 = mulx_u64 b0 s h0 in
  let l1 = mulx_u64 b1 s h1 in
  let l2 = mulx_u64 b2 s h2 in
  let l3 = mulx_u64 b3 s h3 in

  let c = 0uy in
  let c = addcarry_u64 c l1 h0 l1 in
  let c = addcarry_u64 c l2 h1 l2 in
  let c = addcarry_u64 c l3 h2 l3 in
  let c = addcarry_u64 c 0uL h3 l4 in

  let l4 = mulx_u64 l4 38uL h4 in
  let c = 0uy in
  let c = addcarry_u64 c l0 l4 l0 in
  let c = addcarry_u64 c l1 h4 l1 in
  let c = addcarry_u64 c l2 0uL l2 in
  let c = addcarry_u64 c l3 0uL l3 in

  let l4 = 38uL *^ (FStar.Int.Cast.uint8_to_uint64 c) in
  let c = 0uy in
  let c = addcarry_u64 c l0 l4 l0 in
  let c = addcarry_u64 c l1 0uL l1 in
  let c = addcarry_u64 c l2 0uL l2 in
  let c = addcarry_u64 c l3 0uL l3 in

  a.(0ul) <- l0;
  a.(1ul) <- l1;
  a.(2ul) <- l2;
  a.(3ul) <- l3

#reset-options "--lax"

assume val fmul:
  output:felem ->
  input1:felem ->
  input2:felem ->
  Stack unit
    (requires (fun h -> live h output /\ live h input1 /\ live h input2))
    (ensures (fun h0 _ h1 -> True))

[@"c_inline"]
val fsquare:
  input:felem ->
  Stack unit
    (requires (fun h -> live h input))
    (ensures (fun h0 _ h1 -> True))
[@"c_inline"]
let fsquare input = fmul input input input

val fsquare_times:
  output:felem ->
  input:felem{disjoint output input} ->
  count:U32.t{U32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> True))
[@"substitute"]
let fsquare_times output input count =
  blit input 0ul output 0ul 5ul;
  fsquare output;
  let inv h i = True in
  C.Loops.for 1ul count inv (fun i ->
    fsquare output
  )
  
val fsquare_times_inplace:
  output:felem ->
  count:U32.t{U32.v count > 0} ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
[@"substitute"]
let fsquare_times_inplace output count =
  fsquare output;
  let inv h i = True in
  C.Loops.for 1ul count inv (fun i ->
    fsquare output
  )
