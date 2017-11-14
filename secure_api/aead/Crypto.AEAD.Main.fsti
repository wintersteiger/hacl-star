module Crypto.AEAD.Main

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.UInt32
open FStar.HyperStack.ST
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module I = Crypto.Indexing
module Plain = Crypto.Plain

module Bytes = Crypto.Symmetric.Bytes

module P = FStar.Pointer

(* Several constants that the interface relies on *)
type eternal_region = rgn:HH.rid{HS.is_eternal_region rgn}

type lbuffer (l:nat) = Bytes.lbuffer l
type bytes = Bytes.bytes
type lbytes (l:nat) = Bytes.lbytes l

let ivlen (a:I.cipherAlg) = 12ul

let taglen = 16ul

let iv (alg:I.cipherAlg) =
  let open FStar.Mul in
  n:UInt128.t{ UInt128.v n < pow2 (8 * v (ivlen alg)) }

let aadmax =
  assert_norm (2000 <= pow2 32 - 1);
  2000ul //more than enough for TLS

type aadlen_32 = l:UInt32.t {l <=^ aadmax}

(* maximum plain length with which clients can call encrypt/decrypt *)
(* AR: there is currently no bound in Crypto.Plain *)
//val max_plain_len :nat

type plainLen = n:Plain.plainLen //{n <= max_plain_len}

val keylen  :I.id -> UInt32.t
val statelen:I.id -> UInt32.t

type adata = b:bytes{Seq.length b <= v aadmax}
type cipher (i:I.id) (l:nat) = lbytes (l + v taglen)

val entry :i:I.id -> Type0
let nonce (i:I.id) = iv (I.cipherAlg_of_id i)

val mk_entry (#i:I.id): nonce:nonce i -> ad:adata -> #l:plainLen -> p:Plain.plain i l -> c:cipher i l -> entry i

val entry_injective (#i:I.id)
                    (n:nonce i) (n':nonce i) (ad:adata) (ad':adata)
                    (#l:plainLen) (#l':plainLen) (p:Plain.plain i l) (p':Plain.plain i l')
                    (c:cipher i l) (c':cipher i l')
  :Lemma (let e  = mk_entry n ad p c in
          let e' = mk_entry n' ad' p' c' in
          (e == e' <==> (n == n' /\ ad == ad' /\ l == l' /\ p == p' /\ c == c')))

val nonce_of_entry (#i:_) (e:entry i) :nonce i
val plain_of_entry (#i:_) (e:entry i) :(l:plainLen & Plain.plain i l)

let safeMac (i:I.id) = Flag.safeHS i && Flag.mac1 i
let safeId  (i:I.id) = Flag.safeId i

val aead_state : I.id -> I.rw -> Type0

(* AR: CF suggested if this could be GTot *)
val aead_region: #i:_ -> #rw:_ -> aead_state i rw -> GTot eternal_region

(** setting up footprints **)

(*
 * writer footprint is mod_set of aead_region
 * CF/AR: dynamic allocation of subregions?
 * this talks about all subregions, irrespective of whether they are allocated/alive
 *)
let writer_footprint (#i:_) (#rw:_) (st:aead_state i rw) :GTot P.loc
  = P.loc_regions (HH.mod_set (Set.singleton (aead_region st)))

(*
 * shared reader writer footprint is abstract
 * it is the PRF table ref, which we don't want to expose to the clients
 *)
val shared_rw_footprint (#i:_) (#rw:_) (st:aead_state i rw) :GTot P.loc

//writer footprint includes shared_rw_footprint
val lemma_writer_fp_inclues_reader_fp (#i:_) (#rw:_) (st:aead_state i rw)
  :Lemma (requires True) (ensures (P.loc_includes (writer_footprint st) (shared_rw_footprint st)))

(** aead log, monotonicity, and framing w.r.t. read footprint **)

val log: #i:_ -> #rw:_ -> s:aead_state i rw{safeMac i} -> HS.mem -> GTot (Seq.seq (entry i))

(*****)
let is_prefix_of (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a) :Type0
  = Seq.length s1 <= Seq.length s2 /\
    (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)} i < Seq.length s1 ==> Seq.index s1 i == Seq.index s2 i)  //AR: note the pattern
(*****)

val log_prefix (#i:_) (#rw:_) (s:aead_state i rw{safeMac i}) (es:Seq.seq (entry i)) :Type0

val witness_log (#i:_) (#rw:_) (s:aead_state i rw{safeMac i})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ log_prefix s (log s h0)))

val recall_log (#i:_) (#rw:_) (s:aead_state i rw{safeMac i}) (es:Seq.seq (entry i))
  :ST unit (requires (fun _       -> log_prefix s es))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ es `is_prefix_of` (log s h0)))

//reader does not write to the AEAD log
val lemma_frame_log_shared_rw_footprint (#i:_) (#rw:_) (st:aead_state i rw{safeMac i}) (h0 h1:HS.mem)
  :Lemma (requires (P.modifies (shared_rw_footprint st) h0 h1))
         (ensures  (log st h0 == log st h1))

//abstract invariant
val aead_invariant: #i:_ -> #rw:_ -> aead_state i rw -> HS.mem -> Type0

(*
 * AR: move to Pointers
 *)
val unchanged (loc:P.loc) (h0 h1:HS.mem) :Type0

(*
 * invariant only depends on the footprint
 * adding log invariance per CF's suggestion
 *)
val lemma_frame_invariant_and_log_writer_footprint (#i:_) (#rw:_) (st:aead_state i rw) (h0 h1:HS.mem)
  :Lemma (requires (aead_invariant st h0 /\ unchanged (writer_footprint st) h0 h1))
         (ensures  (aead_invariant st h1 /\ (safeMac i ==> log st h0 == log st h1)))

//leaving this abstract for now; but it should imply Crypto.AEAD.Invariant.safelen i len (otp_offset i)
val safelen: I.id -> plainLen -> bool  //AR: safelen is a plainLen?
let ok_plain_len_32 (i:I.id) = l:UInt32.t{v l <= max_plain_len /\ safelen i (v l)}

(*** The main stateful API ***)

(** Allocating a writer **)
(*
 * CF/AR: pass in the parent region and allocate yourself so that
 * freshness is guaranteed, else caller has to guarantee freshness for
 * it to be usable. This is what is done for all nesting allocations so
 * far, so for uniformity reasons too.
 *)
val gen (i:I.id) (parent_rgn:eternal_region)
  :ST (aead_state i I.Writer)
      (requires (fun h -> True))
      (ensures  (fun h0 s h1 ->
                 let r = aead_region s in
                 (r <> HH.root                                 /\  //seems overhead ...
		  HH.parent r == parent_rgn                   /\  //aead region is a child of the input region
		  stronger_fresh_region (aead_region s) h0 h1 /\  //aead region is fresh
		  P.modifies (writer_footprint s) h0 h1       /\  //only modifes the rgn transitiviely
                  (safeMac i ==> log s h1 == Seq.createEmpty) /\  //log is empty initially
                  aead_invariant s h1)))                         //invariant holds

(** building a reader from a writer **)

val genReader (#i: I.id) (wr: aead_state i I.Writer)
 : ST (aead_state i I.Reader)
  (requires (fun h -> aead_invariant wr h))
  (ensures  (fun h0 rd h1 ->
             h0 == h1                               /\  //AR: check
             aead_region rd == aead_region wr       /\
	     shared_rw_footprint rd == shared_rw_footprint wr))

(** [coerce]: only needed for modeling the adversary *)
val coerce (i: I.id) (rgn: eternal_region) (key: lbuffer (v (keylen i)))
  : ST  (aead_state i I.Writer)
        (requires (fun h ->
                   ~ (Flag.prf i) /\
                   Buffer.live h key))
        (ensures  (fun h0 st h1 -> P.modifies_0 h0 h1 /\ aead_invariant st h1))  //AR: check usage of P

(** [leak]: only needed for modeling the adversary *)
val leak (#i: I.id) (st: aead_state i I.Writer)
  : ST (lbuffer (v (statelen i)))
       (requires (fun _ -> ~(Flag.prf i)))
       (ensures  (fun h0 _ h1 -> P.modifies_0 h0 h1 /\ aead_invariant st h1))  //AR: check usage of P

//enc_dec_separation: calling AEAD.encrypt/decrypt requires this separation
//these disjointness conditions should be formulated in terms of P
let enc_dec_separation (#i:_) (#rw:_) (st:aead_state i rw)
                       (#aadlen:nat) (aad: lbuffer aadlen)
                       (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                       (#cipherlen: nat) (cipher:lbuffer cipherlen) =
    Buffer.disjoint aad cipher /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher /\
    HH.disjoint_regions (Set.as_set [Buffer.frameOf (Plain.as_buffer plain);
                                     Buffer.frameOf cipher;
                                     Buffer.frameOf aad])
                        (Set.as_set [aead_region st]) /\
    Buffer.frameOf cipher <> HH.root /\
    Buffer.frameOf aad <> HH.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root
    (* HS.is_eternal_region (Buffer.frameOf cipher) /\ // why? *)
    (* HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\ //why? *)
    (* HS.is_eternal_region (Buffer.frameOf aad) /\ //why? *)

let enc_dec_liveness (#i:_) (#rw:_) (st:aead_state i rw)
                     (#aadlen:nat) (aad: lbuffer aadlen)
                     (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                     (#cipherlen: nat) (cipher:lbuffer cipherlen) (h:HS.mem) =
    let open HS in
    Buffer.live h aad /\
    Buffer.live h cipher /\
    Plain.live h plain /\
    aead_region st `is_in` h.h

let entry_of
          (#i: I.id)
           (n: iv (I.cipherAlg_of_id i))
     (#aadlen: aadlen_32)
         (aad: lbuffer (v aadlen))
   (#plainlen: ok_plain_len_32 i)
       (plain: Plain.plainBuffer i (v plainlen))
  (cipher_tag: lbuffer (v plainlen + v taglen))
           (h: HS.mem) : GTot (entry i) =
  let aad = Buffer.as_seq h aad in
  let p = Plain.sel_plain h plainlen plain in
  let c = Buffer.as_seq h cipher_tag in
  mk_entry n aad p c

let entry_for_nonce (#i:_) (#rw:_) (n:nonce i) (st:aead_state i rw) (h:HS.mem{safeMac i})
  : GTot (option (entry i)) =
    Seq.find_l (fun e -> nonce_of_entry e = n) (log st h)

let fresh_nonce (#i:_) (#rw:_) (n:nonce i) (st:aead_state i rw) (h:HS.mem{safeMac i}) =
  None? (entry_for_nonce n st h)

//AR: integrate buffers and locs?
let loc_of_buffer (#a:Type) (b:Buffer.buffer a) :GTot P.loc
  = P.loc_addresses (Buffer.frameOf b) (Set.singleton (Buffer.as_addr b))

val encrypt
          (i: I.id)
         (st: aead_state i I.Writer)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
      (plain: Plain.plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST unit
  (requires (fun h ->
             enc_dec_separation st aad plain cipher_tag /\
             enc_dec_liveness st aad plain cipher_tag h /\
             aead_invariant st h /\
             (safeMac i ==> fresh_nonce n st h)))
  (ensures (fun h0 _ h1 ->
            P.modifies (P.loc_union (writer_footprint st)
	                            (loc_of_buffer cipher_tag)) h0 h1 /\
            enc_dec_liveness st aad plain cipher_tag h1 /\
            aead_invariant st h1 /\
            (safeMac i ==>
             log st h1 == Seq.snoc (log st h0) (entry_of n aad plain cipher_tag h1))))

val decrypt
          (i: I.id)
         (st: aead_state i I.Reader)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
       (plain: Plain.plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST bool
  (requires (fun h ->
             enc_dec_separation st aad plain cipher_tag /\
             enc_dec_liveness st aad plain cipher_tag h /\
             aead_invariant st h))
  (ensures (fun h0 verified h1 ->
            aead_invariant st h1 /\
            enc_dec_liveness st aad plain cipher_tag h1 /\
            P.modifies (P.loc_union (shared_rw_footprint st)
	                            (loc_of_buffer (Plain.as_buffer plain))) h0 h1 /\
            (safeId i /\ verified ==> entry_for_nonce n st h1 == Some (entry_of n aad plain cipher_tag h1))))

(****************)
// module TSet = FStar.TSet

// type tset (a:Type) = TSet.set a

// (* scaffolding for defining footprint *)
// type address = nat
// let addr_unused_in (rid:HH.rid) (a:address) (m0:HS.mem) =
//   let open FStar.HyperStack in
//   FStar.Monotonic.Heap.addr_unused_in a (Map.sel m0.h rid)

// let contains_addr (rid:HH.rid) (a:address) (m:HS.mem) = ~ (addr_unused_in rid a m)
// let fresh_addresses (rid:HH.rid) (addrs:tset address) (m0:HS.mem) (m1:HS.mem) =
//   forall a. a `TSet.mem` addrs ==>
//        addr_unused_in rid a m0 /\
//        contains_addr  rid a m1

// noeq
// type refs_in_region =
//   | AllRefs : refs_in_region
//   | SomeRefs: tset address -> refs_in_region

// type fp = tset (HH.rid * refs_in_region)
// val footprint: #i:_ -> #rw:_ -> aead_state i rw -> fp

// let regions_of_fp (fp:fp) = TSet.map fst fp
// let refs_of_region (rgn:HH.rid) (footprint:fp) :tset refs_in_region =
//   TSet.map snd (TSet.filter (fun r -> fst r == rgn) footprint)

// //HH only provides modifies on sets, not tsets
// val hh_modifies_t (_:tset HH.rid) (h0:HS.mem) (h1:HS.mem) :Type0

// let modifies_fp (fp:fp) (h0:HS.mem) (h1:HS.mem) :Type0 =
//   let open FStar.HyperStack in
//   hh_modifies_t (regions_of_fp fp) h0 h1 /\
//   (forall r. r `TSet.mem` (regions_of_fp fp) ==> (
//         let refs = refs_of_region r fp in
//         (forall a. a `TSet.mem` refs ==>
//               (match a with
//               | AllRefs -> True
//               | SomeRefs addrs -> FStar.Heap.modifies_t addrs (Map.sel h0.h r) (Map.sel h1.h r)))))

// let preserves_fp (fp:fp) (h0:HS.mem) (h1:HS.mem) :Type0 =
//   let open FStar.HyperStack in
//   (forall r. r `TSet.mem` regions_of_fp fp ==> (
//         let refs = refs_of_region r fp in
//         (forall a. a `TSet.mem` refs ==> (
//               let mod_refs =
//                 match a with
//                 | AllRefs -> TSet.empty
//                 | SomeRefs addrs -> TSet.complement addrs
// 	      in
//               FStar.Heap.modifies_t mod_refs (Map.sel h0.h r) (Map.sel h1.h r)))))

//val as_set': #a:Type -> list a -> Tot (TSet.set a)
//let as_set (#a:Type) (l:list a) :TSet.set a = TSet.as_set' #a l
