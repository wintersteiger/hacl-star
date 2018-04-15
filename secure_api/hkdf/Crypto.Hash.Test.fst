module Crypto.Hash.Test

open FStar.UInt32 
open FStar.HyperStack.All
open FStar.Seq
open FStar.Buffer 
open Crypto.Hash 

module ST = FStar.HyperStack.ST

// sanity check: the low-level API yields the same result as the basic one

[@"c_inline"] // due to variable-length stack allocation
val compute': 
  a: alg13 ->
  len: UInt32.t -> 
  text: lbptr (v len) -> 
  tag: lbptr (tagLength a){ disjoint text tag } -> Stack unit
  (requires fun h0 -> 
    live h0 text /\ live h0 tag)
  (ensures fun h0 () h1 -> 
    live h1 text /\ live h1 tag /\
    modifies_1 tag h0 h1 /\
    v len <= maxLength a /\ (* required for subtyping the RHS below *)
    as_seq h1 tag = spec a (as_seq h0 text))

#reset-options "--max_fuel 0 --z3rlimit 100"
[@"c_inline"] // due to variable-length stack allocation
let compute' a len data tag = 
  push_frame();
  let acc = Buffer.create (state_zero a) (state_size a) in 
  assert_norm(v len <= maxLength a);
  let ll = len %^ blockLen a in
  let lb = len -^ ll  in
  let blocks = sub data 0ul lb in
  let last = offset data lb in
  let h1 = ST.get() in 
  init a acc; 
  update_multi a acc blocks lb; 
  update_last a acc last len;
  extract a acc tag;
  let h2 = ST.get() in 
  pop_frame();
  ( let vblocks = Buffer.as_seq h1 blocks in 
    let vlast = as_seq h1 last in 
    let vsuffix = suffix a (v len) in
    Seq.lemma_eq_intro (as_seq h1 data) (vblocks @| vlast);
    lemma_hash2 (acc0 #a) vblocks (vlast @| vsuffix); 
    Seq.append_assoc vblocks vlast vsuffix )

val compute: 
  a: alg13 ->
  len: UInt32.t -> 
  text: lbptr (v len) -> 
  tag: lbptr (tagLength a){ disjoint text tag } -> Stack unit
  (requires fun h0 -> 
    live h0 text /\ live h0 tag)
  (ensures fun h0 () h1 -> 
    live h1 text /\ live h1 tag /\
    modifies_1 tag h0 h1 /\
    v len <= maxLength a /\ (* required for subtyping the RHS below *)
    as_seq h1 tag = spec a (as_seq h0 text))
let compute a len test tag = 
  match a with 
  | SHA256 -> compute a len test tag
  | SHA384 -> compute a len test tag
  | SHA512 -> compute a len test tag 
  
// we could similarly provide a shared implementation of 
// the [update_multi loop from [update]

val test: a: alg13 -> len: UInt32.t -> input: lbptr (v len) -> Stack unit
  (requires fun h0 -> 
    length input = v len /\
    live h0 input)
  (ensures fun h0 _ h1 -> modifies_0 h0 h1)

let test a len data = 
  push_frame();
  let tag0 = create 0uy (tagLen a) in
  let tag1 = create 0uy (tagLen a) in
  Crypto.Hash.compute a len data tag0;
  compute a len data tag1;
  pop_frame()
