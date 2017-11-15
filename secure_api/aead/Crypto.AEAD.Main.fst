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

//open the implementation files of AEAD
open Crypto.AEAD
open Crypto.AEAD.Invariant
open Crypto.AEAD.Encrypt
open Crypto.AEAD.Decrypt

open Crypto.Symmetric.PRF
module PRF = Crypto.Symmetric.PRF

(* AR: keylen and statelen should be in the fsti, else how are the clients supposed to use them *)
(* AR: also, they should be defined once in some file, and other modules in AEAD should use it from there *)

let keylen i =
  let aux = function
    | I.AES128   -> 16ul
    | I.AES256   -> 32ul
    | I.CHACHA20 -> 32ul
  in
  aux (I.cipherAlg_of_id i)

let statelen i =
  let aux = function
    | I.AES128   -> 432ul // 256 + 176
    | I.AES256   -> 496ul // 256 + 240
    | I.CHACHA20 -> 32ul
  in
  aux (I.cipherAlg_of_id i)

let entry i = aead_entry i

let mk_entry #i nonce ad #l p c = AEADEntry nonce ad l p c

let entry_injective #i n n' ad ad' #l #l' p p' c c' = ()

let nonce_of_entry #i e = AEADEntry?.nonce e

let plain_of_entry #i e = (| AEADEntry?.l e, AEADEntry?.p e |)

let aead_state i rw = aead_state i rw

let aead_region #i #rw st = AEADState?.log_region st

let shared_rw_footprint #i #rw st =
  let fp = P.loc_regions (Set.singleton st.prf.mac_rgn) in
  if Flag.prf i then P.loc_union fp (P.loc_addresses st.prf.mac_rgn (Set.singleton (HS.as_addr (PRF.itable i st.prf))))
  else fp

let lemma_writer_fp_inclues_reader_fp #i #rw st = ()

let log #i #rw st h = HS.sel h (st_ilog st)

(* AR: admitting the monotonicity of the AEAD log, since needs changes in the underlying files *)
let log_prefix #i #rw st es = admit ()

let witness_log #i #rw st = admit ()

let recall_log #i #rw st es = admit ()

let lemma_frame_log_shared_rw_footprint #i #rw st h0 h1 = ()

// let keylen i = PRF.keylen i
// let statelen i = PRF.statelen i
// let entry i = Invariant.aead_entry i
// let mk_entry #i n ad #l p c = Invariant.AEADEntry n ad l p c
// let entry_injective (#i:I.id)
//                     (n:nonce i) (n':nonce i)
//                     (ad:adata) (ad':adata)
//                     (#l:Plain.plainLen) (#l':Plain.plainLen)
//                     (p:Plain.plain i l) (p':Plain.plain i l')
//                     (c:cipher i (Seq.length (Plain.as_bytes p))) (c':cipher i (Seq.length (Plain.as_bytes p')))
//   : Lemma (let e  = mk_entry n ad p c in
//            let e' = mk_entry n' ad' p' c' in
//            (e == e' <==> (n == n' /\ ad == ad' /\ l == l' /\ p == p' /\ c == c')))
//   = ()
// let nonce_of_entry (#i:_) (e:entry i) = Crypto.AEAD.Invariant.AEADEntry?.nonce e

// let aead_state i rw = Invariant.aead_state i rw
// let log_region #i #rw st = Invariant.AEADState?.log_region st
// let prf_region #i #rw st = Invariant.AEADState?.log_region st //TODO: FIXME!!
// let log #i #rw s h = HS.sel h (Invariant.st_ilog s)

// let footprint #i #rw s = TSet.empty //TODO: FIXME!
// let hh_modifies_t (_:FStar.TSet.set HH.rid) (h0:HS.mem) (h1:HS.mem) = True //TODO: FIXME!

// let safelen (i:I.id) (n:nat) = Invariant.safelen i n (Invariant.otp_offset i)
// let invariant #i #rw s h = Invariant.inv s h
// let frame_invariant #i #rw st h0 h1 = admit() //TODO: FIXME!

// let gen i prf_rgn log_rgn =
//     assume false;
//     Crypto.AEAD.gen i log_rgn

// let genReader #i st =
//     assume false;
//     Crypto.AEAD.genReader #i st

// let coerce i rgn key =
//     assume false;
//     Crypto.AEAD.coerce i rgn key

// let leak #i st
//   = assume false;
//     Crypto.AEAD.leak #i st


// let encrypt i st n aadlen aad plainlen plain cipher_tag
//   = assume false;
//     Crypto.AEAD.encrypt i st n aadlen aad plainlen plain cipher_tag

// let decrypt i st n aadlen aad plainlen plain cipher_tag
//   = assume false;
//     Crypto.AEAD.Decrypt.decrypt i st n aadlen aad plainlen plain cipher_tag
