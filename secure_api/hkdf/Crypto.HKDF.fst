module Crypto.HKDF

/// 18-03-04 to be compared to Hashing.HKDF, salvaged as a spec 

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

open Crypto.Hash 

(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HMAC = Crypto.HMAC

(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t
let uint32_p = Buffer.buffer uint32_t
let uint8_p  = Buffer.buffer uint8_t

type alg = Hash.alg13

// ADL July 4
#set-options "--lax"

let hkdf_extract a prk salt saltlen ikm ikmlen =
  HMAC.compute a prk salt saltlen ikm ikmlen

[@"c_inline"]
private val hkdf_expand_inner:
  a       : alg ->
  state   : uint8_p ->
  prk     : uint8_p {Hash.tagLength a <= length prk} ->
  prklen  : uint32_t {v prklen = length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen = length info} ->
  n       : uint32_t {v n <= pow2 8}->
  i       : uint32_t {v i <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 prk /\ live h0 info))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let rec hkdf_expand_inner a state prk prklen info infolen n i =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Recompute the sizes and position of the intermediary objects *)
  (* Note: here we favour readability over efficiency *)
  let size_Ti  = Hash.tagLen  a in
  let size_Til = size_Ti +^ infolen +^ 1ul in
  let size_T = U32.mul_mod n size_Ti in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Retrieve the memory for local computations. state =  Ti | Til | T *)
  let ti = Buffer.sub state pos_Ti size_Ti in
  let til = Buffer.sub state pos_Til size_Til in
  let t = Buffer.sub state pos_T size_T in

  if i = 1ul then begin

    Buffer.blit info 0ul til 0ul infolen;
    Buffer.upd til infolen (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.compute a ti prk prklen til (infolen +^ 1ul);

    (* Store the resulting block in T *)
    Buffer.blit ti 0ul t 0ul size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end

  else if i <=^ n then begin

    (* Concatenate T(i-1) | Info | i *)
    Buffer.blit ti 0ul til 0ul size_Ti;
    Buffer.blit info 0ul til size_Ti infolen;
    Buffer.upd til (size_Til -^ 1ul) (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.compute a ti prk prklen til size_Til;

    (* Store the resulting block in T *)
    let pos = U32.mul_mod (i -^ 1ul) size_Ti in
    Buffer.blit ti 0ul t pos size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end
  else ();

  (* Pop the memory frame *)
  (**) pop_frame()


let hkdf_expand a okm prk prklen info infolen len =
  push_frame ();
  let size_Ti = tagLen a in 
  (* Compute the number of blocks necessary to compute the output *)
  // ceil
  let n_0 = if len %^ size_Ti = 0ul then 0ul else 1ul in
  let n = len /^ size_Ti +^ n_0 in

  (* Describe the shape of memory used by the inner recursive function *)
  let size_Til = size_Ti +^ infolen +^ 1ul in
  let size_T = n *^ size_Ti in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Allocate memory for inner expansion state: Ti @| Til @| T *)
  let state = Buffer.create 0uy (tagLen a +^ size_Til +^ size_T) in

  (* Call the inner expension function *)
  if n >^ 0ul then
    hkdf_expand_inner a state prk prklen info infolen n 1ul;

  (* Extract T from the state *)
  let _T = Buffer.sub state pos_T size_T in

  (* Redundant copy the desired part of T *)
  Buffer.blit _T 0ul okm 0ul len;

  pop_frame()


//18-03-05 I'd rather verify a simpler implementation, closer to the spec
//18-03-05 We could make do with fewer loop variables if it helps with C.Loops
private val hkdf_expand_loop: 
  a       : alg13 ->
  okm     : bptr ->
  prk     : bptr {disjoint okm prk} ->
  prklen  : bptrlen prk ->
  infolen : UInt32.t -> 
  len     : bptrlen okm { v len <= 255 * tagLength a } ->
  hashed  : lbptr (tagLength a + v infolen + 1) {disjoint hashed okm /\ disjoint hashed prk} ->
  i       : UInt8.t {i <> 0uy} ->
  Stack unit
  (requires fun h0 -> 
    live h0 okm /\ live h0 prk /\ live h0 hashed)
  (ensures  fun h0 r h1 -> 
    live h1 okm /\ modifies_2 okm hashed h0 h1 /\ (
    let prk = as_seq h0 prk in 
    let info = as_seq h0 (Buffer.sub hashed (tagLen a) infolen) in 
    let last = if i = 1uy then Seq.createEmpty else as_seq h0 (Buffer.sub hashed 0ul (tagLen a)) in 
    let okm = as_seq h1 okm in 
    okm =  expand0 a prk info (v len) (UInt8.v i) last))


[@"c_inline"]
let rec hkdf_expand_loop a okm prk prklen infolen len hashed i =
  push_frame ();

  let tlen = tagLen a in 
  let tag = Buffer.sub hashed 0ul tlen in 

  // derive one more block
  Buffer.upd hashed (tlen +^ infolen) i;
  if i = 1uy then (
    // the first input is shorter, does not include the chaining block
    let len1 = infolen +^ 1ul in 
    let hashed1 = Buffer.sub hashed tlen len1 in
    HMAC.compute a hashed prk prklen hashed1 len1 )
  else
    HMAC.compute a hashed prk prklen hashed (tlen +^ infolen +^ 1ul);

  // copy it to the result, and iterate if required
  if len <=^ tlen then 
    Buffer.blit tag 0ul okm 0ul len 
  else (
    Buffer.blit tag 0ul okm 0ul tlen;
    let len = len -^ tlen in 
    let okm = Buffer.sub okm tlen len in 
    let i = FStar.UInt8.(i +^ 1uy) in 
    hkdf_expand_loop a okm prk prklen infolen len hashed i);
    
  pop_frame()


[@"c_inline"]
let hkdf_expand_alt a okm prk prklen info infolen len = 
  push_frame();
  let tlen = tagLen a in 
  let hashed = Buffer.create 0uy (tlen +^ infolen +^ 1ul) in 
  Buffer.blit info 0ul hashed tlen infolen; 
  hkdf_expand_loop a okm prk prklen infolen len hashed 1uy;
  pop_frame()



