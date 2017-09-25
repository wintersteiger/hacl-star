module Crypto.AEAD.FileTransfer
open FStar.HyperStack.ST
module AEAD = Crypto.AEAD.Main
module HH = FStar.HyperHeap
module I = Crypto.Indexing
module P = FStar.Pointer

noeq 
type pre_id = {
  reader_id : I.id;
  writer_id : I.id
}

type id = x:pre_id{x.reader_id =!= x.writer_id}

let peer_id (x:id) : id = {
  reader_id=x.writer_id;
  writer_id=x.reader_id
}

val my_nonce   : id -> nonce
val my_region  : id -> mem -> GTot (option region)

val peers_nonce: id -> nonce
val peers_region: id -> mem -> GTot (option region)

noeq 
type conn (i:id) : Type0

//We need a max_plain_len from AEAD

let plain_fragment (i:id) = l:Plain.plainLen{l < max_plain_len} & Plain.plain i.writer_id l

//projection of the AEAD log
val writer_log : i:_ -> conn i -> mem -> Seq.seq (plain_fragment i)

//Maybe useful to have a variant of this that allows you to snapshot
//a sub-sequence of the log corresponding to a file that was sent
val writer_log_contains : i:_ -> conn i -> Seq.seq (plain_fragment i) -> Type0

val witness_writer_log : i:_ -> conn i -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ writer_log_contains c (writer_log c h1)))

val recall_writer_log_contains: i:_ -> c:conn i -> s:Seq.seq (plain_fragment i) -> ST unit
  (requires (fun _ -> write_log_contains c s))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ s `is_a_prefix_of` writer_log c h1))
  
//Maybe it's useful to have some notion of append-only growth of witness_writer_log

//val all_connnections :  we need this table to describe disjointness properties of all connections

val invariant : #i:_ -> conn i -> mem -> Type0 (* basically a conjunction of 2 AEAD invariants *)

val footprint : #i:_ -> conn i -> P.loc

val invariant_frame_unrelated: #i:_ -> c:conn i -> h0:mem -> h1:mem -> Lemma
   (requires (invariant c h0 /\
              loc_unchanged (footprint c) h0 h1)) //Q: how to express loc_unchanged? Does not seem to be in P
   (requires (invariant c h1))

val fragment (#i:_) (#file_size_in_bytes:nat) (file:plain i file_size_in_bytes) : Seq.seq (plain_fragment i)
val rebuild  (#i:_) (frags:Seq.seq (plain_fragment i)) : (l:nat & plain i l)
val fragment_rebuild_inv (#i:_) (#file_size_in_bytes:nat) (file:plain i file_size_in_bytes) :
    Lemma (rebuild (fragment file) == (| file_size_in_bytes, file |))

val send : #i:_ -> #file_size_in_bytes:nat
         -> c:conn i
         -> file:plain i file_size_in_bytes
         -> ST unit
   (requires (fun h -> invariant c h /\
                    global_inv h))
   (ensures (fun h0 _ h1 -> 
               modifies_loc (footprint c) h0 h1 /\
               invariant c h1 /\
               global_inv h1 /\
               (safeId i ==> 
                writer_log c h1 == Seq.append (write_log c h0) (fragment file))))


val recv : #i:_
         -> c:conn i
         -> ST (option (file_size_in_bytes:nat & plain i file_size_in_bytes))
   (requires (fun h -> invariant c h /\
                    global_inv h))
   (ensures (fun h0 f h1 -> 
               modifies_loc (footprint c) h0 h1 /\
               invariant c h1 /\
               global_inv h1 /\
               (safeId i ==> writer_log c h1 == writer_log c h0 /\
                             (match f with 
                              | None -> True
                              | Some (| size, file |) -> 
                                writer_log_contains c (fragment file)))))



let gen (i:id) (writer_region:rid) :
  ST (conn i)
     (requires (fun h -> safeId i ==> Some writer_region == nonce_to_region.[my_nonce i] /\
                      global_inv h0))
     (ensures (fun h0 c h1 -> modifies global_region h0 h1 /\
                           MkConn?.w = writer_region /\
                           global_inv h1 /\
                           conn_inv c h))

