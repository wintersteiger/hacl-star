module Crypto.Hash.Test

open FStar.UInt32 
open FStar.HyperStack.All
open FStar.Seq
open FStar.Buffer 
open Crypto.Hash 

module ST = FStar.HyperStack.ST

// sanity check: the low-level API yields the same result as the basic one

val compute256:
  len: UInt32.t -> 
  text: lbptr (v len) -> 
  tag: lbptr (tagLength SHA256){ disjoint text tag } -> Stack unit
  (requires fun h0 -> 
    live h0 text /\ live h0 tag)
  (ensures fun h0 () h1 -> 
    live h1 text /\ live h1 tag /\
    modifies_1 tag h0 h1 /\
    v len <= maxLength SHA256 /\ (* required for subtyping the RHS below *)
    as_seq h1 tag = spec SHA256 (as_seq h0 text))

#reset-options "--max_fuel 0 --z3rlimit 100"
let compute256 len data tag = 
  push_frame();
  let a: alg13 = SHA256 in 
  let acc = Buffer.create 0ul (state_size a) in 
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


val test: len: UInt32.t -> input: lbptr (v len) -> Stack unit
  (requires fun h0 -> 
    Buffer.length input = v len /\
    Buffer.live h0 input)
  (ensures fun h0 _ h1 -> Buffer.modifies_0 h0 h1)

let test len data = 
  push_frame();
  let a = SHA256 in 
  let tag0 = Buffer.create 0uy (tagLen a) in
  let tag1 = Buffer.create 0uy (tagLen a) in
  compute a len data tag0;
  compute256 len data tag1;
  pop_frame()
