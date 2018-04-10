(* Agile HMAC *)
module Crypto.HMAC

/// Agile specification

type alg = Hash.alg13

open FStar.Seq 

noextract 
let wrap (a:alg) (key: bseq{Seq.length key <= maxLength a}): 
  Tot (lbseq (blockLength a))
= 
  let key0 = if length key <= blockLength a then key else hash a key in 
  let paddingLength = blockLength a - length key0 in 
  key0 @| Seq.create paddingLength 0uy

private let wrap_lemma (a: alg) (key: bseq{Seq.length key <= maxLength a}): Lemma
  (requires length key > blockLength a)
  (ensures wrap a key == (
    let key0 = hash a key in
    let paddingLength = blockLength a - length key0 in 
    key0 @| Seq.create paddingLength 0uy)) = ()

noextract let rec xor (v: bseq) (x: UInt8.t): lbseq (length v) = 
  init (length v) (fun i -> FStar.UInt8.logxor (index v i) x) 
//  Spec.Loops.seq_map (fun y -> FStar.UInt8.logxor x y) v
//18-04-08 not sure why the latter fails.


// [noextract] incompatible with interfaces?!
let hmac a key data =
  assert(tagLength a + blockLength a <= maxLength a); // avoid?
  let k = wrap a key in 
  let h1 = spec a (xor k 0x36uy @| data) in
  let h2 = spec a (xor k 0x5cuy @| h1) in 
  h2

/// Agile implementation, relying on 3 variants of SHA2 supported by
/// HACL*.

open FStar.HyperStack.All
open FStar.Buffer
open FStar.UInt32

module ST = FStar.HyperStack.ST

(* we rely on the output being zero-initialized for the correctness of padding *)
[@"substitute"]
val wrap_key:
  a: alg ->
  output: lbptr (blockLength a) ->
  key: bptr {length key <= maxLength a /\ disjoint output key} ->
  len: UInt32.t {v len = length key} ->
  Stack unit
    (requires (fun h0 -> 
      live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (blockLength a) 0uy ))
    (ensures  (fun h0 _ h1 -> 
      live h1 output /\ live h1 key /\ live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (blockLength a) 0uy /\
      modifies_1 output h0 h1 /\
      as_seq h1 output = wrap a (as_seq h0 key) ))

[@"substitute"]
let wrap_key a output key len =
  let i = if len <=^ blockLen a then len else tagLen a in 
  let nkey = Buffer.sub output 0ul i in 
  let pad = Buffer.sub output i (blockLen a -^ i) in
  let h0 = ST.get () in
  if len <=^ blockLen a then 
    Buffer.blit key 0ul nkey 0ul len
  else 
    Hash.compute a len key nkey;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h0 pad) (Seq.create (blockLength a - v i) 0uy);
  Seq.lemma_split (as_seq h1 output) (v i)

// we pre-allocate the variable-type, variable length hash state,
// to avoid both verification and extraction problems.

[@"substitute"]
val part1:
  a: alg ->
  acc: state a -> ( 
  let uint = if a = SHA256 then UInt32.t else UInt64.t in 
  s2: lbptr (blockLength a) ->
  data: bptr {
    length data + blockLength a  < pow2 32 /\ 
    length data + blockLength a  <= maxLength a /\ 
    disjoint data s2} ->
  len: UInt32.t {length data = v len} ->
  Stack unit
    (requires (fun h0 -> 
      disjoint #uint acc s2 /\ 
      disjoint #uint acc data /\ 
      live #uint h0 acc /\ 
      live h0 s2 /\ live h0 data))
    (ensures  (fun h0 _ h1 -> 
      live h1 s2 /\ live h0 s2 /\ live h1 data /\ live h0 data /\ 
      modifies_2 #uint acc s2 h0 h1 /\ (
      let hash0 = Seq.slice (as_seq h1 s2) 0 (tagLength a) in
      hash0 == spec a (Seq.append (as_seq h0 s2) (as_seq h0 data))))))

#reset-options "--max_fuel 0 --z3rlimit 1000"
[@"substitute"]
let part1 a (acc: state a) keyblock data len =
  Math.Lemmas.lemma_div_mod (v len) (blockLength a);
  let n0 = len /^ blockLen a in
  let r0 = len %^ blockLen a in
  let data_blocks = Buffer.sub data 0ul (n0 *^ blockLen a) in
  let data_last = Buffer.offset data (n0 *^ blockLen a) in
  Hash.init a acc;  
  Hash.update a acc keyblock;
  let h1 = ST.get() in 
  Hash.update_multi a acc data_blocks (n0 *^ blockLen a);
  let h2 = ST.get() in
  Hash.update_last a acc data_last (blockLen a +^ len);
  let h3 = ST.get() in
  let tag = Buffer.sub keyblock 0ul (tagLen a) in (* Salvage memory *)
  Hash.extract a acc tag; 
  (
    let v1 = as_seq h1 keyblock in 
    let vblocks = as_seq h1 data_blocks in 
    let acc1 = as_acc h1 acc in 
    lemma_compress (acc0 #a) v1;
    assert(acc1 == hash0 #a v1);
    let v2 = v1 @| vblocks in 
    let acc2 = as_acc h2 acc in 
    lemma_hash2 (acc0 #a) v1 vblocks;
    assert(acc2 == hash0 #a v2);
    let vdata = as_seq h1 data in  
    let vlast = as_seq h1 data_last in 
    let vsuffix = suffix a (blockLength a + v len) in 
    Seq.lemma_eq_intro vdata (vblocks @| vlast);
    let acc3 = as_acc h3 acc in 
    lemma_hash2 (acc0 #a) v2 (vlast @| vsuffix); 
    assert(acc3 == hash0 #a (v2 @| (vlast @| vsuffix)));
    Seq.append_assoc v2 vlast vsuffix; 
    Seq.append_assoc v1 vblocks vlast;
    assert(acc3 == hash0 #a ((v1 @| vdata) @| vsuffix));
    assert(finish acc3 == spec a (v1 @| vdata)))
  
// the two parts have the same stucture; let's keep their proofs in sync. 
[@"substitute"]
val part2:
  a: alg ->
  acc: state a -> ( 
  let uint = if a = SHA256 then UInt32.t else UInt64.t in 
  mac: lbptr (tagLength a) ->
  opad: lbptr (blockLength a) ->
  tag: lbptr (tagLength a) {disjoint mac opad /\ disjoint mac tag} ->
  Stack unit
    (requires fun h0 -> 
      disjoint #uint acc opad /\ 
      disjoint #uint acc tag /\ 
      disjoint #uint acc mac /\ 
      live #uint h0 acc /\ 
      live h0 mac /\ live h0 opad /\ live h0 tag)
    (ensures fun h0 _ h1 -> 
      live h1 mac /\ live h0 mac /\ modifies_2 #uint acc mac h0 h1 /\
      ( let payload = Seq.append (as_seq h0 opad) (as_seq h0 tag) in 
        Seq.length payload <= maxLength a /\
        as_seq h1 mac = spec a payload)))

[@"substitute"]
let part2 a acc mac opad tag =
  let totLen = blockLen a +^ tagLen a in 
  assert_norm(v totLen <= maxLength a);
  Hash.init a acc;
  Hash.update a acc opad; 
  let h1 = ST.get() in 
  Hash.update_last a acc tag totLen;
  let h2 = ST.get() in 
  Hash.extract a acc mac;
  (
    let v1 = as_seq h1 opad in
    let acc1 = as_acc h1 acc in 
    lemma_compress (acc0 #a) v1;
    assert(acc1 == hash0 #a v1);
    let vtag = as_seq h1 tag in 
    let vsuffix = suffix a (blockLength a + tagLength a) in
    let acc2 = as_acc h2 acc in 
    lemma_hash2 (acc0 #a) v1 (vtag @| vsuffix); 
    Seq.append_assoc v1 vtag vsuffix;
    assert(acc2 == hash0 #a ((v1 @| vtag) @| vsuffix));
    assert(finish acc2 = spec a (v1 @| vtag)))

// similar spec as hmac with keylen = blockLen a 
val hmac_core:
  a: alg ->
  acc: state a -> (
  let uint = if a = SHA256 then UInt32.t else UInt64.t in 
  tag: lbptr (tagLength a) ->
  key: lbptr (blockLength a) {disjoint key tag} ->
  data: bptr{
    length data + blockLength a < pow2 32 /\ 
    length data + blockLength a <= maxLength a /\
    disjoint data key } ->
  datalen: UInt32.t {v datalen = length data} ->
  Stack unit
  (requires fun h0 -> 
    disjoint #uint acc tag /\ 
    disjoint #uint acc key /\ 
    disjoint #uint acc data /\ 
    live #uint h0 acc /\ 
    live h0 tag /\ live h0 key /\ live h0 data)
  (ensures fun h0 _ h1 ->   
    live h1 tag /\ live h0 tag /\
    live h1 key /\ live h0 key /\
    live h1 data /\ live h0 data /\ 
    //modifies_2 #uint acc tag h0 h1 /\
    ( let k = as_seq h0 key in  
      let k1 = xor k 0x36uy in
      let k2 = xor k 0x5cuy in
      let v1 = spec a (k1 @| as_seq h0 data) in 
      Seq.length (k2 @| v1) <= maxLength a /\
      as_seq h1 tag = spec a (k2 @| v1))))
      //harder: hmac a (as_seq h0 key) (as_seq h0 data)

// todo functional correctness.
// below, we only XOR with a constant bytemask.
val xor_bytes_inplace:
  a: bptr ->
  b: bptr{ disjoint a b } ->
  len: UInt32.t {v len = length a /\ v len = length b} ->
  Stack unit
  (requires fun h0 -> live h0 a /\ live h0 b)
  (ensures fun h0 _ h1 -> 
    modifies_1 a h0 h1)
let xor_bytes_inplace a b len =     
  C.Loops.in_place_map2 a b len (fun x y -> UInt8.logxor x y)

// TODO small improvement: part1 and part2 return their result in acc
// so that we can reuse the pad.
let hmac_core a acc mac key data len =
  push_frame ();
  let ipad = Buffer.create 0x36uy (blockLen a) in
  let opad = Buffer.create 0x5cuy (blockLen a) in
  xor_bytes_inplace ipad key (blockLen a);
  xor_bytes_inplace opad key (blockLen a);
  let h0 = ST.get() in
  part1 a acc ipad data len; 
  let h1 = ST.get() in 
  let inner = Buffer.sub ipad 0ul (tagLen a) in (* salvage memory *)
  part2 a acc mac opad inner;
  let h2 = ST.get() in 
  ( 
    let k = as_seq h0 key in  
    let k1: lbseq (blockLength a) = xor k 0x36uy in
    let k2: lbseq (blockLength a) = xor k 0x5cuy in
    let vdata = as_seq h0 data in 
    let v1: lbseq (tagLength a) = as_seq h1 inner in 
    assert_norm(blockLength a + tagLength a <= maxLength a);
    assert(Seq.length (k2 @| v1) <= maxLength a);
    let v2 = as_seq h2 mac in 

    assume(as_seq h0 ipad = k1); 
    assume(as_seq h1 opad = k2);
    assert(v1 == spec a (k1 @| vdata));
    assert(v2 == spec a (k2 @| v1)));
  pop_frame ()
  

// not much point in separating hmac_core? verbose, but it helps
// monomorphise stack allocations.

let compute a mac key keylen data datalen =
  push_frame (); 
  let keyblock = Buffer.create 0x00uy (blockLen a) in
  assert_norm(pow2 32 <= maxLength a);
  wrap_key a keyblock key keylen;
  ( match a with 
  | SHA256 -> 
      push_frame();
      let acc = Buffer.create 0ul (state_size a) in 
      hmac_core SHA256 acc mac keyblock data datalen;
      pop_frame()
  | SHA384 -> 
      push_frame();
      let acc = Buffer.create 0UL (state_size a) in 
      hmac_core SHA384 acc mac keyblock data datalen;
      pop_frame()
  | SHA512 -> 
      push_frame();
      let acc = Buffer.create 0UL (state_size a) in 
      hmac_core SHA512 acc mac keyblock data datalen;
      pop_frame());
  pop_frame ()

 
