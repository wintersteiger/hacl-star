module EverCrypt.Hash

/// ----------agile implementation of hash specification ------------
/// must be in scope for linking the agile spec to the ad hoc algorithmic specs

//18-08-01 required for re-typechecking the .fsti :(
#set-options "--z3rlimit 200"

let string_of_alg =
  let open C.String in function
  | MD5    -> !$"MD5"
  | SHA1   -> !$"SHA1"
  | SHA224 -> !$"SHA224"
  | SHA256 -> !$"SHA256"
  | SHA384 -> !$"SHA384"
  | SHA512 -> !$"SHA512"

let type_of a =
  match a with
  | MD5 | SHA1 | SHA224 | SHA256 -> UInt32.t // uint_32
  | SHA384 | SHA512              -> UInt64.t // uint_64

let size_of_k a: nat =
  match a with
  | SHA256 -> 64
  | SHA384 -> 80
  | _      -> 0 //TBC

type acc (a:alg) = {
  k: Seq.lseq (type_of a) (size_of_k a);
  hash: Seq.lseq (type_of a) 8;
  counter: nat;
}

// 18-07-10 in principle k would suffice.
let acc0 #a =
  match a with
  | SHA256 -> {
      hash = EverCrypt.Spec.SHA2_256.h_0;
      k = EverCrypt.Spec.SHA2_256.k;
      counter = 0
    }
  | SHA384 -> {
      hash = EverCrypt.Spec.SHA2_384.h_0;
      k = EverCrypt.Spec.SHA2_384.k;
      counter = 0
    }
  | _ -> {
      hash = Seq.create 8 (if a = SHA512 then 0UL else 0ul);
      k = Seq.empty;
      counter = 0
    }


// 18-07-06 We need a fully-specified refinement: the hacl* spec
// should state that the counter is incremented by 1 and that the K
// constant is unchanged---a total spec would also save the need for
// stateful invariants.
//
// Besides, all of that could be avoided if the state was just the
// intermediate hash.

let compress #a st b =
  match a with
  | SHA256 ->
     { k       = EverCrypt.Spec.SHA2_256.k;
       hash    = EverCrypt.Spec.SHA2_256.update st.hash b;
       counter = st.counter + 1 }
  | SHA384 ->
     { k       = EverCrypt.Spec.SHA2_384.k;
       hash    = EverCrypt.Spec.SHA2_384.update st.hash b;
       counter = st.counter + 1 }
  | _ -> st //TBC

// using the same be library as in hacl*; to be reconsidered.
// 18-07-10 why do I need type annotations? why passing the same constant 3 types?
let extract #a st =
  match a with
  | SHA224 -> Spec.Lib.uint32s_to_be 7 (Seq.slice st.hash 0 7)
  | SHA256 -> Spec.Lib.uint32s_to_be 8 st.hash
  | SHA384 -> Spec.Lib.uint64s_to_be 6 (Seq.slice st.hash 0 6)
  | SHA512 -> Spec.Lib.uint64s_to_be 8 st.hash
  | _      -> Seq.slice (Spec.Lib.uint32s_to_be 8 st.hash) 0 (tagLength a) //TBC

//#set-options "--z3rlimit 500"
//18-07-12 this immediately verifies from the .fsti :(
let rec lemma_hash2 #a a0 b0 b1 = admit()
(*
  if Seq.length b0 = 0 then (
    Seq.lemma_empty b0;
    Seq.append_empty_l b1 )
  else (
    let c,b0' = Seq.split b0 (blockLength a) in
    let c',b' = Seq.split (Seq.append b0 b1) (blockLength a) in
    Seq.append_assoc c b0' b1;
    Seq.lemma_split b0 (blockLength a);
    Seq.lemma_eq_intro (Seq.append b0 b1) (Seq.append c' b');
    Seq.lemma_eq_intro c c';
    Seq.lemma_eq_intro b' (Seq.append b0' b1);
    lemma_hash2 (hash2 a0 c) b0' b1)
*)

let suffix a l =
  let l1 = l % blockLength a in
  let l0 = l - l1 in
  assert(l0 % blockLength a = 0);
  match a with
  | SHA256 ->
      assert_norm(maxLength a < Spec.SHA2_256.max_input_len_8);
      let pad = Spec.SHA2_256.pad l0 l1 in
      // 18-07-06 the two specs have different structures
      assume(Seq.length pad = suffixLength a l);
      pad
  | SHA384 ->
      assume False;
      // not sure what's wrong with this branch
      //assume(maxLength a < Spec.SHA2_384.max_input_len_8);
      let pad = Spec.SHA2_384.pad l0 l1 in
      assume(Seq.length pad = suffixLength a l);
      pad
  | _ -> admit()

/// 18-04-07 postponing verified integration with HACL* for now. We
/// provide below a concise definition of the Merkle-Damgard
/// construction. The plan is to integrate it with Benjamin's
/// algorithmic specifications. At that point, we will probably hide
/// the construction behind the provider interface (since we don't
/// care about the construction when using or reasoning about them).
///
/// ----------agile implementation of hash specification ------------

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module T = LowStar.ToFStarBuffer

module AC = EverCrypt.AutoConfig
module SC = EverCrypt.StaticConfig

module Vale = EverCrypt.Vale
module Hacl = EverCrypt.Hacl
module ValeGlue = EverCrypt.ValeGlue
module OpenSSL = EverCrypt.OpenSSL

module ST = FStar.HyperStack.ST
module MP = LowStar.ModifiesPat

open LowStar.BufferOps
open FStar.Integers

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

noeq type state_s: Type0 =
| SHA256_Hacl: p:uint32_p{ B.freeable p /\ B.length p = v Hacl.SHA2_256.size_state }   -> state_s
| SHA256_Vale: p:uint32_p{ B.freeable p /\ B.length p = v ValeGlue.sha256_size_state } -> state_s
| SHA384_Hacl: p:uint64_p{ B.freeable p /\ B.length p = v Hacl.SHA2_384.size_state }   -> state_s
| HASH_OPENSSL: st:Dyn.dyn -> p:uint8_p{B.freeable p /\ B.length p = 1} -> a:alg -> state_s

let alg_of = function
  | SHA256_Hacl _ -> SHA256
  | SHA256_Vale _ -> SHA256
  | SHA384_Hacl _ -> SHA384
  | HASH_OPENSSL _ _ a -> a

let footprint_s (s: state_s) =
  match s with
  | SHA256_Hacl p -> M.loc_addr_of_buffer p
  | SHA256_Vale p -> M.loc_addr_of_buffer p
  | SHA384_Hacl p -> M.loc_addr_of_buffer p
  | HASH_OPENSSL _ p _ -> M.loc_addr_of_buffer p

#set-options "--max_fuel 0 --max_ifuel 1"

let invariant_s s h =
  match s with
  | SHA256_Hacl p -> B.live h p
  | SHA256_Vale p -> B.live h p
  | SHA384_Hacl p -> B.live h p
  | HASH_OPENSSL _ p _ -> B.live h p

//#set-options "--z3rlimit 40"

let repr s h : GTot _ =
  let s = B.get h s 0 in
  // 18-08-30 regression after moving ghosts around; strange MD5 error?!
  assume False;
  match s with
  | SHA256_Hacl p ->
      let p = T.new_to_old_ghost p in
      {
        k = Hacl.SHA2_256.slice_k h p;
        hash = Hacl.SHA2_256.slice_hash h p;
        counter = Hacl.SHA2_256.counter h p
      }
  | SHA256_Vale p ->
      {
        k = ValeGlue.sha256_slice_k h p;
        hash = ValeGlue.sha256_slice_hash h p;
        counter = ValeGlue.sha256_counter h p
      }
  | SHA384_Hacl p ->
      let p = T.new_to_old_ghost p in
      {
        k = Hacl.SHA2_384.slice_k h p;
        hash = Hacl.SHA2_384.slice_hash h p;
        counter = Hacl.SHA2_384.counter h p
      }
  | _ -> admit()

let repr_eq (#a:alg) (r1 r2: acc a) =
  Seq.equal r1.k r2.k /\
  Seq.equal r1.hash r2.hash /\
  r1.counter = r2.counter

let fresh_is_disjoint l1 l2 h0 h1 = ()

let invariant_loc_in_footprint s m = ()

let frame_invariant l s h0 h1 =
  let state = B.deref h0 s in
  assume (B.deref h1 s == state); // FIXME Immutablebuffer
  assert (repr_eq (repr s h0) (repr s h1))

// C.Failure.failwith ensures True
// but we mainly use it to rule out impossible
// code paths that depend on dynamic configuration
// and are not proved statically
let failwith (#a:Type) (s:C.String.t) : ST a
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> False)
  = assume false; C.Failure.failwith s

let create a =
  let s: state_s a =
    match a with
    | SHA256 ->
      let i = AC.sha256_impl () in
      if SC.vale && i = AC.Vale then
        let b = B.malloc HS.root 0ul ValeGlue.sha256_size_state in
        SHA256_Vale b
      else if SC.hacl && i = AC.Hacl then
        let b = B.malloc HS.root 0ul Hacl.SHA2_256.size_state in
        SHA256_Hacl b
      else if SC.openssl && i = AC.OpenSSL then
        let st = OpenSSL.hash_create OpenSSL.SHA256 in
	let p = B.malloc HS.root 0uy 1ul in
	HASH_OPENSSL st p a
      else
        failwith !$"inconsistent configuration"
    | SHA384 ->
      let i = AC.sha384_impl () in
      if SC.hacl && i = AC.Hacl then
        let b = B.malloc HS.root 0UL Hacl.SHA2_384.size_state in
        SHA384_Hacl b
      else if SC.openssl && i = AC.OpenSSL then
        let st = OpenSSL.hash_create OpenSSL.SHA384 in
	let p = B.malloc HS.root 0uy 1ul in
	HASH_OPENSSL st p a
      else
        failwith !$"inconsistent configuration"
    | SHA512 ->
      let i = AC.sha512_impl () in
      if SC.openssl && i = AC.OpenSSL then
        let st = OpenSSL.hash_create OpenSSL.SHA512 in
	let p = B.malloc HS.root 0uy 1ul in
	HASH_OPENSSL st p a
      else
        failwith !$"inconsistent configuration"
    | MD5 | SHA1 | SHA224 ->
      if SC.openssl then
        let a' = match a with
	  | MD5 -> OpenSSL.MD5
	  | SHA1 -> OpenSSL.SHA1
	  | SHA224 -> OpenSSL.SHA224 in
        let st = OpenSSL.hash_create a' in
	let p = B.malloc HS.root 0uy 1ul in
	HASH_OPENSSL st p a
      else
        failwith !$"not implemented"
  in
  B.malloc HS.root s 1ul

let has_k (#a:alg) (st:acc a) =
  match a with
  | SHA256 -> st.k == EverCrypt.Spec.SHA2_256.k
  | SHA384 -> st.k == EverCrypt.Spec.SHA2_384.k
  | _ -> True

let rec lemma_hash2_has_k
  (#a:alg)
  (v:acc a {has_k v})
  (b:bytes {Seq.length b % blockLength a = 0}):
  GTot (_:unit{has_k (hash2 v b)}) (decreases (Seq.length b))
=
  if Seq.length b = 0 then
    assert_norm(hash2 v b == v)
  else
    let c,b' = Seq.split b (blockLength a) in
    Seq.lemma_eq_intro b (Seq.append c b');
    lemma_hash2_has_k (compress v c) b';
    lemma_hash2 v c b';
    lemma_compress v c
    // assert(Seq.length b' % blockLength a = 0);
    // assert(has_k (compress v c));
    // assert(hash2 v b == hash2 (compress v c) b')

let lemma_hash0_has_k #a b = lemma_hash2_has_k (acc0 #a) b

let rec lemma_has_counter (#a:alg) (b:bytes {Seq.length b % blockLength a = 0}):
  GTot (_:unit{
    blockLength a <> 0 /\
    (hash0 #a b).counter == Seq.length b / blockLength a}) (decreases (Seq.length b))
=
  admit() //TODO, similar, unnecessary once we get rid of the internal counter

#set-options "--max_fuel 0"
let init s =
  match !*s with
  | SHA256_Hacl p ->
    assert_norm(acc0 #SHA256 == hash0 #SHA256 (Seq.empty #UInt8.t));
    Hacl.SHA2_256.init (T.new_to_old_st p)
  | SHA384_Hacl p ->
    assert_norm(acc0 #SHA384 == hash0 #SHA384 (Seq.empty #UInt8.t));
    Hacl.SHA2_384.init (T.new_to_old_st p)
  | SHA256_Vale p ->
    assume false;
    ValeGlue.sha256_init p // hashing empty
  | HASH_OPENSSL _ _ _ ->
    assume false;
    () // hashing empty

#set-options "--z3rlimit 20 --print_implicits"
let update prior s data =
  let h0 = ST.get() in
  (
    let prior = Ghost.reveal prior in 
    let a = alg_of (B.deref h0 s) in
    let r0 = repr s h0 in
    let fresh = B.as_seq h0 data in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_compress #a r0 fresh;
    lemma_hash2 #a (acc0 #a) prior fresh;
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
    if SC.hacl then
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_256.update p data
    else failwith !$"impossible"
    
  | SHA384_Hacl p ->
    if SC.hacl then
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_384.update p data
    else failwith !$"impossible"

  | SHA256_Vale p ->
    if SC.vale then
     begin
      assume false; // TODO: functional correctness
      ValeGlue.sha256_update p data
     end
    else failwith !$"impossible"
      
  | HASH_OPENSSL st _ a ->
    if SC.openssl then
     begin
      assume false; // TODO: functional correctness
      OpenSSL.hash_update st data (blockLen a)
     end
    else failwith !$"impossible"

#set-options "--z3rlimit 300"
let update_multi prior s data len =
  let h0 = ST.get() in
  (
    let prior = Ghost.reveal prior in
    let a = alg_of (B.deref h0 s) in
    let r0 = repr s h0 in
    let fresh = B.as_seq h0 data in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter + v len / blockLength a < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
      let n = len / blockLen SHA256 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // let h = ST.get() in assume(bounded_counter s h (v n));
      Hacl.SHA2_256.update_multi p data n;

      let h1 = ST.get() in
      (
        let a = alg_of (B.deref h1 s) in
        let r0 = repr #a s h0 in
        let r1 = repr #a s h1 in
        let fresh = Buffer.as_seq h0 data in
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_256.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh));
      ()

  | SHA384_Hacl p ->
      let n = len / blockLen SHA384 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      //let h = ST.get() in assume(bounded_counter s h (v n));
      Hacl.SHA2_384.update_multi p data n;

      let h1 = ST.get() in
      (
        let a = alg_of (B.deref h1 s) in
        let r0 = repr #a s h0 in
        let r1 = repr #a s h1 in
        let fresh = Buffer.as_seq h0 data in
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_384.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh));
      ()

  | SHA256_Vale p ->
    if SC.vale then
     begin
      let n = len / blockLen SHA256 in
      assume false; // Functional correctness
      ValeGlue.sha256_update_multi p data n
     end
    else failwith !$"impossible"

  | HASH_OPENSSL st _ _ ->
    if SC.openssl then
     begin
      assume false; // Functional correctness
      OpenSSL.hash_update st data len
     end
    else failwith !$"impossible"

//18-07-07 For SHA384 I was expecting a conversion from 32 to 64 bits

//18-07-10 WIP verification; still missing proper spec for padding
let update_last prior s data totlen =
  let h0 = ST.get() in
  ( 
    let a = alg_of (B.deref h0 s) in
    let r0 = repr s h0 in
    let pad = suffix a (v totlen) in
    let prior = Ghost.reveal prior in
    let fresh = Seq.append (B.as_seq h0 data) pad in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    // lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter + 2 < pow2 32 - 1);
    assert(M.(loc_disjoint (footprint #a s h0) (loc_buffer data))));
  match !*s with
  | SHA256_Hacl p ->
    if SC.hacl then
      let len = totlen % blockLen SHA256 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_256.update_last p data len;
      let h1 = ST.get() in
      ( 
        let a = alg_of (B.deref h1 s) in
        let pad = suffix a (v totlen) in
        let prior = Ghost.reveal prior in
        let fresh = Seq.append (Buffer.as_seq h0 data) pad in
        assert(Seq.length fresh % blockLength a = 0);
        let b = Seq.append prior fresh in
        assume(repr s h1 == hash0 b) // Hacl.Spec misses at least the updated counter
      )
    else failwith !$"impossible"
      
  | SHA384_Hacl p ->
    if SC.hacl then
     begin
      let len = totlen % blockLen SHA384 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      assume false; // TODO: functional correctness
      Hacl.SHA2_384.update_last p data len
     end
    else failwith !$"impossible"

  | SHA256_Vale p ->
    if SC.vale then
     begin
      let len = totlen % blockLen SHA256 in
      assume false; // TODO: functional correctness
      ValeGlue.sha256_update_last p data len
     end
    else failwith !$"impossible"
    
  | HASH_OPENSSL st _ a ->
    if SC.openssl then
     begin
      assume(false); // TODO: functional correctness
      OpenSSL.hash_update st data (totlen % (blockLen a))
     end
    else failwith !$"impossible"

let finish s dst =
  match !*s with
  | SHA256_Hacl p ->
    if SC.hacl then
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      Hacl.SHA2_256.finish p dst
    else failwith !$"impossible"
  | SHA384_Hacl p ->
    if SC.hacl then
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      Hacl.SHA2_384.finish p dst
    else failwith !$"impossible"
  | SHA256_Vale p ->
    if SC.vale then
     begin
      assume false; // TODO: functional correctness
      ValeGlue.sha256_finish p dst
     end
    else failwith !$"impossible"
  | HASH_OPENSSL st _ _ ->
    if SC.openssl then
     begin
      assume false; // TODO: functional correctness
      let _ = OpenSSL.hash_final st dst in ()
     end
    else failwith !$"impossible"

let free s =
  (match !* s with
  | SHA256_Hacl p -> B.free p
  | SHA384_Hacl p -> B.free p
  | SHA256_Vale p -> B.free p
  | HASH_OPENSSL st p _ -> OpenSSL.hash_free st; B.free p);
  B.free s

private let hash_openssl a dst input len
  : ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> False) =
  assume false; // Functional correctness
  if SC.openssl then
   let a' = match a with
   | MD5 -> OpenSSL.MD5
   | SHA1 -> OpenSSL.SHA1
   | SHA224 -> OpenSSL.SHA224
   | SHA256 -> OpenSSL.SHA256
   | SHA384 -> OpenSSL.SHA384
   | SHA512 -> OpenSSL.SHA512 in
   let st = OpenSSL.hash_create a' in
   OpenSSL.hash_update st input len;
   let _ = OpenSSL.hash_final st dst in
   OpenSSL.hash_free st
  else
    failwith !$"not implemented"

let hash a dst input len =
  match a with
  | SHA256 ->
      let i = AC.sha256_impl () in
      if SC.vale && i = AC.Vale then
       begin
        assume false;
        ValeGlue.sha256_hash dst input len
       end
      else if SC.hacl && i = AC.Hacl then
       begin
        let input = T.new_to_old_st input in
        let dst = T.new_to_old_st dst in
	assume false;
        Hacl.SHA2_256.hash dst input len
       end
      else if SC.openssl && i = AC.OpenSSL then
       hash_openssl SHA256 dst input len
      else failwith !$"not implemented"
  | SHA384 ->
    let i = AC.sha384_impl () in
    if SC.hacl && i = AC.Hacl then
     begin
      let input = T.new_to_old_st input in
      let dst = T.new_to_old_st dst in
      assume false;
      Hacl.SHA2_384.hash dst input len
     end
    else if SC.openssl && i = AC.OpenSSL then
      hash_openssl SHA384 dst input len
    else
      failwith !$"not implemented"
  | a ->
    hash_openssl a dst input len

