module Crypto.AEAD.FileTransfer

open FStar.HyperStack.ST

module AEAD = Crypto.AEAD.Main
module I = Crypto.Indexing
module P = FStar.Pointer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Plain = Crypto.Plain

noeq 
type pre_id = {
  writer_id: I.id;
  reader_id: I.id
}

type id = x:pre_id{x.reader_id =!= x.writer_id}

let peer_id (x:id) :id = {
  writer_id = x.reader_id;
  reader_id = x.writer_id
}

val my_nonce   :i:id -> (AEAD.nonce (i.writer_id))
val my_region  :id -> HS.mem -> GTot (option HH.rid)  //AR: why is this an option?

val peer_nonce :i:id -> (AEAD.nonce (i.reader_id))
val peer_region:id -> HS.mem -> GTot (option HH.rid)

val conn (i:id) :Type0  //adding noeq gives inconsistent qualifiers error

let plain_fragment (i:id) = l:AEAD.plainLen & Plain.plain i.writer_id l

//AR: how do we define this?
val safeId: i:id -> GTot bool

(** log, monotonicity **)

val log_elt (i:id) :Type0

val plain_of_log_elt: #i:_ -> log_elt i -> plain_fragment i

//projection of the AEAD log
val log: #i:_ -> c:conn i{safeId i} -> HS.mem -> GTot (Seq.seq (log_elt i))

//maybe useful to have a variant of this that allows you to snapshot
//a sub-sequence of the log corresponding to a file that was sent
val log_prefix: #i:_ -> c:conn i{safeId i} -> Seq.seq (log_elt i) -> Type0

val witness_log (#i:_) (c:conn i{safeId i})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ log_prefix c (log c h0)))

val recall_log (#i:_) (c:conn i{safeId i}) (s:Seq.seq (log_elt i))
  :ST unit (requires (fun _      -> log_prefix c s))
           (ensures (fun h0 _ h1 -> h0 == h1 /\ s `AEAD.is_prefix_of` (log c h0)))
  
(* basically a conjunction of 2 AEAD invariants *)
val conn_invariant: #i:_ -> conn i -> HS.mem -> Type0

val conn_footprint: #i:_ -> conn i -> GTot P.loc

val lemma_frame_invariant_footprint (#i:_) (c:conn i) (h0 h1:HS.mem)
   :Lemma (requires (conn_invariant c h0 /\
                     P.unchanged (conn_footprint c) h0 h1))
          (ensures  (conn_invariant c h1))

(* fragment a file into fragments that can be passed to AEAD *)
val fragment_file (#i:id) (#len:nat) (file:Plain.plain i.writer_id len) :Seq.seq (plain_fragment i)
val rebuild_file  (#i:id) (s:Seq.seq (plain_fragment i)) :(l:nat & Plain.plain i.writer_id l)
val lemma_fragment_rebuild_inverse (#i:id) (#len:nat) (file:Plain.plain i.writer_id len)
  :Lemma (rebuild_file (fragment_file file) == (| len, file |))

val send (#i:_) (#len:nat) (c:conn i) (file:Plain.plain i.writer_id len)
  :ST unit (requires (fun h0     -> conn_invariant c h0))
           (ensures (fun h0 _ h1 -> P.modifies (conn_footprint c) h0 h1 /\
                                 conn_invariant c h1                 /\
                                 (safeId i ==>
				  (let log0 = log c h0 in
				   let log1 = log c h1 in
				   log0 `AEAD.is_prefix_of` log1          /\
				   AEAD.seq_map (plain_of_log_elt #i)
				                (Seq.slice log1 (Seq.length log0)
				                                (Seq.length log1)) ==
	                           fragment_file file))))

val recv (#i:_) (c:conn i)
  :ST (option (len:nat & Plain.plain i.writer_id len))
      (requires (fun h0      -> conn_invariant c h0))
      (ensures  (fun h0 t h1 -> P.modifies (conn_footprint c) h0 h1 /\
                             conn_invariant c h1                 /\
                             (safeId i ==>
			      (log c h1 == log c h0 /\
                               (match t with 
                                | None -> True
                                | Some (| len, file |) ->
				  (fragment_file file) `AEAD.is_subseq_of`
				  (AEAD.seq_map (plain_of_log_elt #i) (log c h0)))))))



// let gen (i:id) (writer_region:rid) :
//   ST (conn i)
//      (requires (fun h -> safeId i ==> Some writer_region == nonce_to_region.[my_nonce i] /\
//                       global_inv h0))
//      (ensures (fun h0 c h1 -> modifies global_region h0 h1 /\
//                            MkConn?.w = writer_region /\
//                            global_inv h1 /\
//                            conn_inv c h))




//val all_connnections :we need this table to describe disjointness properties of all connections

