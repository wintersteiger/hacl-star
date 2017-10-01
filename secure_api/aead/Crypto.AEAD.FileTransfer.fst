module Crypto.AEAD.FileTransfer

open FStar.HyperStack.ST

module AEAD = Crypto.AEAD.Main
module I = Crypto.Indexing
module P = FStar.Pointer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Plain = Crypto.Plain

let my_nonce    i = magic ()
let my_region   i = magic ()
let peer_nonce  i = magic ()
let peer_region i = magic ()

private noeq type conn_aux (i:id) =
  | C: writer:AEAD.aead_state i.writer_id I.Writer ->
       reader:AEAD.aead_state i.reader_id I.Reader ->
       conn_aux i

let conn i = conn_aux i

let safeId i = magic ()

assume val lemma_safeId (i:id) :Lemma (requires (safeId i)) (ensures (AEAD.safeMac i.writer_id /\
                                                                      AEAD.safeMac i.reader_id))
				      [SMTPat (safeId i)]

let log_elt (i:id)          = AEAD.entry i.writer_id
let plain_of_log_elt #i elt = AEAD.plain_of_entry elt
let log #i c h              = AEAD.log c.writer h
let log_prefix #i c s       = AEAD.log_prefix c.writer s
let witness_log #i c        = AEAD.witness_log c.writer
let recall_log #i c s       = AEAD.recall_log c.writer s

let conn_invariant #i c h =
  let _ = () in
  AEAD.aead_invariant c.writer h /\ AEAD.aead_invariant c.reader h

(*
 * footprint cannot be (write c.writer union read c.reader), else we can't prove framing
 *)
let conn_footprint #i c = P.loc_union (AEAD.write_footprint c.writer) (AEAD.write_footprint c.reader)

let lemma_frame_invariant_footprint #i c h0 h1 =
  AEAD.lemma_frame_invariant_footprint c.writer h0 h1;
  AEAD.lemma_frame_invariant_footprint c.reader h0 h1

let fragment_file #i #len file                  = magic ()
let rebuild_file  #i s                          = magic ()
let lemma_fragment_rebuild_inverse #i #len file = admit ()
