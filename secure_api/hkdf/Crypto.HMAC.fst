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
  let padding = blockLength a - length key0 in 
  key0 @| Seq.create padding 0uy

noextract 
let xor k v = Spec.Loops.seq_map (fun x -> FStar.UInt8.logxor x v) k

// [noextract] incompatible with interfaces?!
let hmac a key data =
  let k = wrap a key in 
  let h1 = hash a (xor k 0x36uy @| data) in 
  let h2 = hash a (xor k 0x5cuy @| h1) in 
  h2


/// Agile implementation, relying on using 3 variants of SHA2
/// supported by HACL*.

open FStar.HyperStack.All
open FStar.Buffer
open FStar.UInt32

module ST = FStar.HyperStack.ST

// ADL lax prototype for QUIC deadline
// 18-03-04 restructured

(* we rely on the output being zero-initialized in case the key is less than a block *)
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

// replaced by [H.compute]; not sure why it required pre-zeroing-out the result.
// let agile_hash (a:alg) (output:uint8_p{length output = tagLength a})
//   (input:uint8_p{length input < maxLength a /\ disjoint output input})
//   (len:uint32_t{v len = length output})
//   : Stack unit
//   (requires fun h -> live h input /\ live h output
//     /\ (as_seq h output) == Seq.create (tagLength a) 0uy)
//   (ensures fun h0 () h1 -> live h1 output /\ live h1 input
//     /\ modifies_1 output h0 h1
//     /\ as_seq h1 input == as_seq h0 input
//     /\ correct_agile_hash a (as_seq h1 input) (as_seq h1 output))
//   =
//   match a with
//   | SHA256 -> Hacl.Hash.SHA2_256.hash output input len
//   | SHA384 -> Hacl.Hash.SHA2_384.hash output input len
//   | SHA512 -> Hacl.Hash.SHA2_512..hash output input len

//#reset-options "--max_fuel 0  --z3rlimit 250"
[@"substitute"]
let wrap_key a output key len =
 (**) let h0 = ST.get () in
  if len <=^ blockLen a then
   begin
    (**) assert(v (blockLen a) - v len >= 0);
    (**) assert(as_seq h0 output == Seq.create (v (blockLen a)) 0uy);
    Buffer.blit key 0ul output 0ul len;
    (**) let h1 = ST.get () in
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h1 output) 0 (v len)) (as_seq h0 key);
    (**) assert(Seq.slice (as_seq h1 output) 0 (v len) == as_seq h0 key);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h1 output) (v len) (v (blockLen a))) (Seq.create (v (blockLen a) - v len) 0uy);
    (**) assert(Seq.slice (as_seq h1 output) (v len) (v (blockLen a)) == Seq.create (v (blockLen a) - v len) 0uy);
    (**) Seq.lemma_eq_intro (as_seq h1 output) (Seq.append (as_seq h0 key) (Seq.create (v (blockLen a) - v len) 0uy));
    (**) assert(as_seq h1 output == Seq.append (as_seq h0 key) (Seq.create (v (blockLen a) - v len) 0uy))
   end
  else
   begin
    (**) assert(v (blockLen a) - tagLength a >= 0);
    (**) assert(as_seq h0 output == Seq.create (v (blockLen a)) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 (tagLength a)) (Seq.create (tagLength a) 0uy);
    (**) assert(Seq.slice (as_seq h0 output) 0 (tagLength a) == Seq.create (tagLength a) 0uy);
    (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) (tagLength a) (v (blockLen a))) (Seq.create (v (blockLen a) - tagLength a) 0uy);
    (**) assert(Seq.slice (as_seq h0 output) (tagLength a) (v (blockLen a)) == Seq.create (v (blockLen a) - tagLength a) 0uy);
    let nkey = Buffer.sub output 0ul (tagLen a) in
    Hash.compute a len key nkey
    (**) //let h1' = ST.get () in
    (**) //assert(as_seq h1' nkey == );
    (**) //assert(Seq.slice (as_seq h1' output) 0 (tagLength a) == Spec_Hash.hash (as_seq h0 key));
    (**) //no_upd_lemma_1 h0 h1' (Buffer.sub output 0ul (tagLen a)) (Buffer.sub output (tagLen a) blockLen a) -^ (tagLen a)));
    (**) //Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h1' output)) (tagLength a) (v (blockLen )) (Seq.create (v (blockLen a) - tagLength a) 0uy);
    (**) //assert(Seq.slice (reveal_sbytes (as_seq h1' output)) (tagLength a) (v (blockLen a)) == Seq.create (v (blockLen a) - tagLength a) 0uy);
    (**) //Seq.lemma_eq_intro (reveal_sbytes (as_seq h1' output)) (Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v (blockLen a) - tagLength a) 0uy));
    (**) //assert(reveal_sbytes (as_seq h1' output) == Seq.append (reveal_sbytes (as_seq h1' nkey)) (Seq.create (v (blockLen a) - tagLength a) 0uy))
   end

(* should not be necessary 
//#reset-options " --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"
let counter_pos: alg -> Tot uint32_t = function
  | SHA256 -> Hacl.Hash.SHA2_256.pos_count_w
  | SHA384 -> Hacl.Hash.SHA2_384.pos_count_w
  | SHA512 -> Hacl.Hash.SHA2_512.pos_count_w

//#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"
let counter_size: alg -> Tot uint32_t = function
  | SHA256 -> Hacl.Hash.SHA2_256.size_count_w
  | SHA384 -> Hacl.Hash.SHA2_384.size_count_w
  | SHA512 -> Hacl.Hash.SHA2_512..size_count_w
*)

(* usage? 
//#reset-options "--max_fuel 0  --z3rlimit 50"
val lemma_alloc:
  a: alg ->
  s: state a ->
  Lemma
    (requires (s == Seq.create (v (state_size a)) 0ul))
    (ensures (
      let seq_counter = Seq.slice s (U32.v (counter_pos a)) (U32.(v (counter_pos a) + v (counter_size a))) in
      let counter = Seq.index seq_counter 0 in
      U32.v counter = 0))
let lemma_alloc a s = ()
*)

//#reset-options "--max_fuel 0  --z3rlimit 20"
[@"substitute"]
val hmac_part1:
  a: alg ->
  s2: lbptr (blockLength a) ->
  data: bptr {length data + blockLength a  < pow2 32 /\ disjoint data s2} ->
  len: UInt32.t {length data = v len} ->
  Stack unit
        (requires (fun h0 ->  live h0 s2 /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 s2 /\ live h0 s2
                             /\ live h1 data /\ live h0 data /\ modifies_1 s2 h0 h1
                             /\ (let hash0 = Seq.slice (as_seq h1 s2) 0 (tagLength a) in
                             hash0 = hash a (Seq.append (as_seq h0 s2) (as_seq h0 data)))))

(*
let agile_alloc (a:alg) : Stack (st:state a)
  (requires fun h -> True)
  (ensures fun h0 () h1 -> True)
  =
  match a with
  | SHA256 -> Buffer.create 0ul (state_size a)
  | SHA384 -> Buffer.create 0uL (state_size a)
  | SHA512 -> Buffer.create 0uL (state_size a)
*)

//18-03-04 the condition on len was probably false; not also the
//calling convention has changed.
// let Hash.update_last (a:alg) (st:state a)
//   (input:uint8_p {length input = v (blockLen a)})
//   (len:uint32_t {v len = length input})
//   : Stack unit (requires fun h -> True)
//   (ensures fun h0 () h1 -> True)
//    //live h1 st /\ modifies_1 st h0 h1)
//   =
//   match a with
//   | SHA256 -> Hacl.Hash.SHA2_256.update_last st input len
//   | SHA384 -> Hacl.Hash.SHA2_384.update_last st input (Int.Cast.uint32_to_uint64 len)
//   | SHA512 -> Hacl.Hash.SHA2_512..update_last st input (Int.Cast.uint32_to_uint64 len)


//#reset-options "--max_fuel 0  --z3rlimit 200"
[@"substitute"]
let hmac_part1 a s2 data len =

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get () in

  (* Allocate memory for the Hash function state *)
  // let state0 = Hash.alloc () in
  let state0 = Buffer.create 0ul (state_size a) in
  (**) let h = ST.get() in
  (**) //lemma_alloc (reveal_h32s (as_seq h state0));
  (**) no_upd_lemma_0 h0 h s2;
  (**) no_upd_lemma_0 h0 h data;

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  (**) assert((blockLen a) <> 0ul);
  (**) Math.Lemmas.lemma_div_mod (v len) (v (blockLen a));
  let n0 = len /^ blockLen a in
  let r0 = len %^ blockLen a in
  let blocks0 = Buffer.sub data 0ul (n0 *^ (blockLen a)) in
  let last0 = Buffer.offset data (n0 *^ (blockLen a)) in
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) 0 (UInt32.v (n0 *^ (blockLen a)))) (as_seq h blocks0);
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h data) (UInt32.v (n0 *^ (blockLen a))) (length data)) (as_seq h last0);
  Hash.init a state0;  
  (**) //let h' = ST.get() in
  (**) //no_upd_lemma_1 h h' state0 s2;
  (**) //no_upd_lemma_1 h h' state0 data;
  (**) //no_upd_lemma_1 h h' state0 blocks0;
  (**) //no_upd_lemma_1 h h' state0 last0;
  Hash.update a state0 s2;
  (**) //let h'' = ST.get() in
  (**) //no_upd_lemma_1 h' h'' state0 blocks0;
  (**) //no_upd_lemma_1 h' h'' state0 last0;
  Hash.update_multi a state0 blocks0 n0;
  (**) //let h''' = ST.get() in
  (**) //no_upd_lemma_1 h'' h''' state0 last0;
  Hash.update_last a state0 last0 len;
  (**) let h1 = ST.get () in

  let h'''' = ST.get() in
  let hash0 = Buffer.sub s2 0ul (tagLen a) in (* Salvage memory *)
  Hash.extract a state0 hash0; (* s4 = hash (s2 @| data) *)
//  (**) Spec_Hash.lemma_hash_all_prepend_block (reveal_sbytes (as_seq h0 s2)) (reveal_sbytes (as_seq h0 data));

  (* Pop the memory frame *)
  (**) pop_frame ()


//#reset-options "--max_fuel 0  --z3rlimit 20"
[@"substitute"]
val hmac_part2:
  a: alg ->
  mac: lbptr (tagLength a) ->
  s5: lbptr (blockLength a) {disjoint s5 mac} ->
  s4: lbptr (tagLength a) {disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
        (requires (fun h -> True)) //live h mac /\ live h s5 /\ live h s4))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac))
 //TODO spec
 ///\ live h1 s5 /\ live h0 s5
 ///\ live h1 s4 /\ live h0 s4 /\ modifies_1 mac h0 h1
 ///\ (reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))))))

//#reset-options "--max_fuel 0  --z3rlimit 200"
[@"substitute"]
let hmac_part2 a mac s5 s4 =
  (**) assert_norm(pow2 32 = 0x100000000);
  (**) let hinit = ST.get() in
  (**) push_frame ();
  (**) let h0 = ST.get () in
  (* Allocate memory for the Hash function state *)
  (* let state1 = Hash.alloc () in *)
  let state1 = Buffer.create 0ul (state_size a) in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  (**) let h = ST.get() in
  (**) no_upd_lemma_0 h0 h s5;
  (**) no_upd_lemma_0 h0 h s4;
  (**) no_upd_lemma_0 h0 h mac;
  (**) //lemma_alloc (reveal_h32s (as_seq h state1));
  Hash.init a state1;
  (**) let h' = ST.get() in
  (**) //assert(let st_h0 = Seq.slice (as_seq h' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
  (**) //reveal_h32s st_h0 == Spec_Hash.h_0);
  (**) no_upd_lemma_1 h h' state1 s5;
  (**) no_upd_lemma_1 h h' state1 s4;
  (**) no_upd_lemma_1 h h' state1 mac;
  Hash.update a state1 s5; (* s5 = opad *)
  (**) let h'' = ST.get() in
  (**) //assert(let st_h0 = Seq.slice (as_seq h'' state1) (U32.v Hash.pos_whash_w) (U32.(v Hash.pos_whash_w + v Hash.size_whash_w)) in
  (**) //       reveal_h32s st_h0 == Spec_Hash.(update h_0 (reveal_sbytes (as_seq h0 s5))));
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(as_seq h'' s4 == as_seq hinit s4);
  Hash.update_last a state1 s4 (blockLen a +^ tagLen a);
  (**) let h''' = ST.get() in
  (**) no_upd_lemma_1 h' h'' state1 s4;
  (**) no_upd_lemma_1 h' h'' state1 mac;
  (**) assert(live h''' mac);
  Hash.extract a state1 mac; //(* s7 = hash (s5 @| s4) *)
  (**) //let h1 = ST.get() in
  (**) //Spec_Hash.lemma_hash_single_prepend_block (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4));
  (**)  //Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 mac)) (Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
  (**) //assert(reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))));
  (**) pop_frame ()

(* same spec as hmac with keylen = blockLen a *)
//#reset-options "--max_fuel 0  --z3rlimit 20"
val hmac_core:
  a: alg ->
  tag: lbptr (tagLength a) ->
  key: lbptr (blockLength a) {disjoint key tag} ->
  data: bptr {length data + blockLength a < pow2 32 /\ disjoint data tag /\ disjoint data key} ->
  datalen: UInt32.t {v datalen = length data} ->
  Stack unit
  (requires (fun h0 -> live h0 tag /\ live h0 key /\ live h0 data))
  (ensures  (fun h0 _ h1 -> 
    live h1 tag /\ live h0 tag /\
    live h1 key /\ live h0 key /\
    live h1 data /\ live h0 data /\ modifies_1 tag h0 h1 /\
    as_seq h1 tag = hmac a (as_seq h0 key) (as_seq h0 data)))

//#reset-options "--max_fuel 0 --z3rlimit 10"
let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len (fun x y -> UInt8.logxor x y)
// below, we only XOR with a constant bytemask.

//#reset-options "--max_fuel 0  --z3rlimit 150"
let hmac_core a mac key data len =
  (**) let h00 = ST.get () in
  (**) push_frame ();
  (**) let h0 = ST.get () in
/// 18-03-03 avoid those and do the xor on copying?
  (* Initialize constants *)
  let ipad = Buffer.create 0x36uy (blockLen a) in
  let opad = Buffer.create 0x5cuy (blockLen a) in
  (**) let h1 = ST.get () in
  (**) //assert(reveal_sbytes (as_seq h1 ipad) == Seq.create (v (blockLen a)) 0x36uy);
  (**) //assert(reveal_sbytes (as_seq h1 opad) == Seq.create (v (blockLen a)) 0x5cuy);

  (* Step 2: xor "result of step 1" with ipad *)
  xor_bytes_inplace ipad key (blockLen a);
  (**) let h2 = ST.get () in
  (**) //assert(reveal_sbytes (as_seq h2 ipad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  hmac_part1 a ipad data len; (* s2 = ipad *)
  let s4 = Buffer.sub ipad 0ul (tagLen a) in (* Salvage memory *)
  (**) let h3 = ST.get () in
  (**) //Seq.lemma_eq_intro (as_seq h3 (Buffer.sub ipad 0ul (tagLen a))) (Seq.slice (as_seq h3 ipad) 0 (tagLength a));
  (**) //assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h2 ipad)) (reveal_sbytes (as_seq h0 data))));
  (**) //assert(reveal_sbytes (as_seq h3 s4) == Spec_Hash.hash (Seq.append (Spec.xor_bytes (reveal_sbytes (as_seq h1 ipad)) (reveal_sbytes (as_seq h0 key))) (reveal_sbytes (as_seq h0 data))));

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes_inplace opad key (blockLen a);
  (**) let h4 = ST.get () in
  (**) //assert(reveal_sbytes (as_seq h4 opad) == Spec.xor_bytes (reveal_sbytes (as_seq h1 opad)) (reveal_sbytes (as_seq h0 key)));

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  hmac_part2 a mac opad s4; (* s5 = opad *)
  (**) let h5 = ST.get () in
  (**) //assert(reveal_sbytes (as_seq h5 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)));
  (**) pop_frame ()

//#reset-options "--max_fuel 0  --z3rlimit 25"
let compute a mac key keylen data datalen =
  push_frame (); 
  let wrapped_key = Buffer.create 0x00uy (blockLen a) in
  wrap_key a wrapped_key key keylen;
  hmac_core a mac wrapped_key data datalen;
  pop_frame ()
