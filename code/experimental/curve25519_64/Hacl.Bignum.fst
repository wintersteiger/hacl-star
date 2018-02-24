module Hacl.Bignum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open FStar.Int.Cast

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Endianness

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

type uint8_p = buffer Hacl.UInt8.t

[@"c_inline"]
val addcarry_u64:
  carry:U8.t -> a:limb -> b:limb ->
  Tot (tuple2 U8.t limb)
let addcarry_u64 carry a b =
  let t1 = add_mod a (uint8_to_uint64 carry) in
  let carry = if U64.(t1 <^ a) then 1uy else 0uy in
  let res = add_mod t1 b in
  let carry = if U64.(res <^ t1) then U8.(carry +^ 1uy) else carry in
  (carry, res)
  
[@"c_inline"]
val subborrow_u64:
  carry:U8.t -> a:limb -> b:limb ->
  Tot (tuple2 U8.t limb)
let subborrow_u64 carry a b =
  let res = sub_mod (sub_mod a b) (uint8_to_uint64 carry) in
  let carry =
      if U8.(carry =^ 1uy) then
	 (if U64.(a <=^ b) then 1uy else 0uy)
      else
         (if U64.(a <^ b) then 1uy else 0uy) in
  (carry, res)

[@"c_inline"]
val mulx_u64:
  a:limb -> b:limb -> Tot (tuple2 limb limb)
let mulx_u64 a b =
  let res = U128.mul_wide a b in
  let r = U128.uint128_to_uint64 res in
  let c = U128.uint128_to_uint64 (U128.shift_right res 64ul) in
  (c, r)

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

  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in

  let top = 19uL *^ (top >>^ 63ul) in
  let c = 0uy in
  let (c, input0) = addcarry_u64 c input0 top in
  let (c, input1) = addcarry_u64 c input1 0uL in
  let (c, input2) = addcarry_u64 c input2 0uL in
  let (c, input3) = addcarry_u64 c input3 0uL in
  
  let output0 = Buffer.sub output 0ul  8ul in
  let output1 = Buffer.sub output 8ul  8ul in
  let output2 = Buffer.sub output 16ul 8ul in
  let output3 = Buffer.sub output 24ul 8ul in
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
  let (c, a0) = addcarry_u64 c a0 b0 in
  let (c, a1) = addcarry_u64 c a1 b1 in
  let (c, a2) = addcarry_u64 c a2 b2 in
  let (c, a3) = addcarry_u64 c a3 b3 in
  
  let top = 38uL *^ (FStar.Int.Cast.uint8_to_uint64 c) in
  let c = 0uy in
  let (c, a0) = addcarry_u64 c a0 top in
  let (c, a1) = addcarry_u64 c a1 0uL in
  let (c, a2) = addcarry_u64 c a2 0uL in
  let (c, a3) = addcarry_u64 c a3 0uL in

  a.(0ul) <- a0;
  a.(1ul) <- a1;
  a.(2ul) <- a2;
  a.(3ul) <- a3

val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> True))
#reset-options "--z3rlimit 50 --max_fuel 0"
[@"substitute" ]
let fdifference a b =
  let a0 = a.(0ul) in let a1 = a.(1ul) in
  let a2 = a.(2ul) in let a3 = a.(3ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in
  let b2 = b.(2ul) in let b3 = b.(3ul) in
   
  let c = 0uy in
  let (c, tmp0) = addcarry_u64 c b0 (uint64_to_limb 0xffffffffffffffdauL) in
  let (c, tmp1) = addcarry_u64 c b1 (uint64_to_limb 0xffffffffffffffffuL) in
  let (c, tmp2) = addcarry_u64 c b2 (uint64_to_limb 0xffffffffffffffffuL) in
  let (c, tmp3) = addcarry_u64 c b3 (uint64_to_limb 0xffffffffffffffffuL) in
  let (c, tmp4) = addcarry_u64 c 0uL 0uL in

  let c = 0uy in
  let (c, tmp0) = subborrow_u64 c tmp0 a0 in
  let (c, tmp1) = subborrow_u64 c tmp1 a1 in 
  let (c, tmp2) = subborrow_u64 c tmp2 a2 in
  let (c, tmp3) = subborrow_u64 c tmp3 a3 in
  let (c, tmp4) = subborrow_u64 c tmp4 0uL in

  let top = U64.mul_mod 38uL tmp4 in
  let c = 0uy in
  let (c, tmp0) = addcarry_u64 c tmp0 top in
  let (c, tmp1) = addcarry_u64 c tmp1 0uL in
  let (c, tmp2) = addcarry_u64 c tmp2 0uL in
  let (c, tmp3) = addcarry_u64 c tmp3 0uL in
  
  let top = U64.mul_mod 38uL (FStar.Int.Cast.uint8_to_uint64 c) in
  let c = 0uy in
  let (c, tmp0) = addcarry_u64 c tmp0 top in
  let (c, tmp1) = addcarry_u64 c tmp1 0uL in
  let (c, tmp2) = addcarry_u64 c tmp2 0uL in
  let (c, tmp3) = addcarry_u64 c tmp3 0uL in
  
  a.(0ul) <- tmp0;
  a.(1ul) <- tmp1;
  a.(2ul) <- tmp2;
  a.(3ul) <- tmp3

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
  
  let (h0, l0) = mulx_u64 b0 s in
  let (h1, l1) = mulx_u64 b1 s in
  let (h2, l2) = mulx_u64 b2 s in
  let (h3, l3) = mulx_u64 b3 s in

  let c = 0uy in
  let (c, l1) = addcarry_u64 c l1 h0 in
  let (c, l2) = addcarry_u64 c l2 h1 in
  let (c, l3) = addcarry_u64 c l3 h2 in
  let (c, l4) = addcarry_u64 c 0uL h3 in

  let (h4, l4) = mulx_u64 l4 38uL in
  let c = 0uy in
  let (c, l0) = addcarry_u64 c l0 l4 in
  let (c, l1) = addcarry_u64 c l1 h4 in
  let (c, l2) = addcarry_u64 c l2 0uL in
  let (c, l3) = addcarry_u64 c l3 0uL in

  let l4 = U64.mul_mod 38uL (FStar.Int.Cast.uint8_to_uint64 c) in
  let c = 0uy in
  let (c, l0) = addcarry_u64 c l0 l4 in
  let (c, l1) = addcarry_u64 c l1 0uL in
  let (c, l2) = addcarry_u64 c l2 0uL in
  let (c, l3) = addcarry_u64 c l3 0uL in

  a.(0ul) <- l0;
  a.(1ul) <- l1;
  a.(2ul) <- l2;
  a.(3ul) <- l3

[@"c_inline"]
val fmul_by_word:
  tmp:buffer Hacl.UInt64.t{length tmp = 8} ->
  input2:felem -> word:limb ->
  j:U32.t -> c:U8.t ->
  h0:limb -> h1:limb -> Stack (tuple2 U8.t limb)
    (requires (fun h -> live h tmp /\ live h input2))
    (ensures (fun h0 _ h1 -> True))
[@"c_inline"]
let rec fmul_by_word tmp input2 word j c h0 h1 =
   if U32.(j <^ 4ul) then begin
     let tmpj = tmp.(j) in
     let (h1, low) = mulx_u64 word input2.(j) in
     let (c, tmpj) = addcarry_u64 c low h0 in
     tmp.(j) <- tmpj;
     fmul_by_word tmp input2 word U32.(j +^ 1ul) c h1 h1
   end else (c, h0)

[@"c_inline"]
val fmul_inner:
  tmp:buffer Hacl.UInt64.t{length tmp = 8} ->
  word:limb -> input2:felem ->
  i:U32.t{U32.v i < 4} -> j:U32.t{U32.v i + U32.v j <= 8} -> c:U8.t -> d:U8.t ->
  h0:limb -> h1:limb -> Stack (tuple2 (tuple2 U8.t U8.t) limb)
    (requires (fun h -> live h tmp /\ live h input2))
    (ensures (fun h0 _ h1 -> True))
let rec fmul_inner tmp word input2 i j c d h0 h1 =
  if U32.(j <^ 4ul) then begin
    let tmpij = tmp.(U32.(i +^ j)) in
    let (h1, low) = mulx_u64 word input2.(j) in
    let (c, h0) = addcarry_u64 c low h0 in
    let (d, tmpij) = addcarry_u64 d tmpij h0 in
    tmp.(U32.(i +^ j)) <- tmpij;
    fmul_inner tmp word input2 i U32.(j +^ 1ul) c d h1 h1
  end else ((c, d), h0)

[@"c_inline"]
val fmul_:
  tmp:buffer Hacl.UInt64.t{length tmp = 8} ->
  input1:felem -> input2:felem ->
  i:U32.t -> c:U8.t -> d:U8.t ->
  h0:limb -> h1:limb -> Stack unit
    (requires (fun h -> live h tmp /\ live h input1 /\ live h input2))
    (ensures (fun h0 _ h1 -> True))  
[@"c_inline"]  
let rec fmul_ tmp input1 input2 i c d h0 h1 =
  if U32.(i <^ 4ul) then begin
    let tmpi = tmp.(i) in
    let input1i = input1.(i) in
    let (h0, low) = mulx_u64 input1i input2.(0ul) in
    let (d, tmpi) = addcarry_u64 d tmpi low in
    tmp.(i) <- tmpi;
    let c = 0uy in    
    let ((c, d), h0) = fmul_inner tmp input1i input2 i 1ul c d h0 h1 in 
    let (c, h0) = addcarry_u64 c h0 0uL in
    let tmpi4 = tmp.(U32.(i +^ 4ul)) in
    let (d, tmpi4) = addcarry_u64 d h0 0uL in
    tmp.(U32.(i +^ 4ul)) <- tmpi4;
    fmul_ tmp input1 input2 U32.(i +^ 1ul) c d h0 h1
  end

[@"c_inline"]
val fmul:
  output:felem ->
  input1:felem ->
  input2:felem ->
  Stack unit
    (requires (fun h -> live h output /\ live h input1 /\ live h input2))
    (ensures (fun h0 _ h1 -> True))
#reset-options "--z3rlimit 50 --max_fuel 0"
[@"c_inline"]
let fmul output input1 input2 =
  push_frame();
  let tmp = create 0uL 8ul in
  let tmp0 = tmp.(0ul) in
  let (h0, tmp0) = mulx_u64 input1.(0ul) input2.(0ul) in
  tmp.(0ul) <- tmp0;
  let c = 0uy in
  let d = 0uy in
  let (c, h0) = fmul_by_word tmp input2 input1.(0ul) 1ul c h0 0uL in
  let tmp4 = tmp.(4ul) in
  let (c, tmp4) = addcarry_u64 c h0 0uL in
  tmp.(4ul) <- tmp4;
  fmul_ tmp input1 input2 1ul c d h0 0uL;

  let tmp0 = tmp.(0ul) in let tmp1 = tmp.(1ul) in
  let tmp2 = tmp.(2ul) in let tmp3 = tmp.(3ul) in
  let tmp4 = tmp.(4ul) in let tmp5 = tmp.(5ul) in
  let tmp6 = tmp.(6ul) in let tmp7 = tmp.(7ul) in

  let c = 0uy in
  let d = 0uy in
  let (h0, low) = mulx_u64 tmp4 38uL in
  let (c, tmp0) = addcarry_u64 c tmp0 low in
  let (h1, low) = mulx_u64 tmp5 38uL in
  let (c, tmp1) = addcarry_u64 c tmp1 low in
  let (d, tmp1) = addcarry_u64 d tmp1 h0 in
  let h0 = h1 in
  let (h1, low) = mulx_u64 tmp6 38uL in
  let (c, tmp2) = addcarry_u64 c tmp2 low in
  let (d, tmp2) = addcarry_u64 d tmp2 h0 in
  let h0 = h1 in
  let (h1, low) = mulx_u64 tmp7 38uL in
  let (c, tmp3) = addcarry_u64 c tmp3 low in
  let (d, tmp3) = addcarry_u64 d tmp3 h0 in

  let (c, h1) = addcarry_u64 c h1 0uL in
  let (d, h1) = addcarry_u64 d h1 0uL in

  let h1 = U64.mul_mod 38uL h1 in
  let c = 0uy in
  let (c, tmp0) = addcarry_u64 c tmp0 h1 in
  let (c, tmp1) = addcarry_u64 c tmp1 0uL in
  let (c, tmp2) = addcarry_u64 c tmp2 0uL in
  let (c, tmp3) = addcarry_u64 c tmp3 0uL in
 
  let h1 = U64.mul_mod 38uL (FStar.Int.Cast.uint8_to_uint64 c) in
  let c = 0uy in
  let (c, tmp0) = addcarry_u64 c tmp0 h1 in
  let (c, tmp1) = addcarry_u64 c tmp1 0uL in
  let (c, tmp2) = addcarry_u64 c tmp2 0uL in
  let (c, tmp3) = addcarry_u64 c tmp3 0uL in

  output.(0ul) <- tmp0;
  output.(1ul) <- tmp1;
  output.(2ul) <- tmp2;
  output.(3ul) <- tmp3;
  pop_frame()

[@"c_inline"]
val fsquare:
  input:felem ->
  Stack unit
    (requires (fun h -> live h input))
    (ensures (fun h0 _ h1 -> True))
[@"c_inline"]
let fsquare input = fmul input input input

#reset-options "--lax"

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
