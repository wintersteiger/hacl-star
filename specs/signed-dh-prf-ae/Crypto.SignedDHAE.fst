module Crypto.SignedDHAE

//module Spec = Spec.SignedDHAE
open Spec.CryptoLib
open Crypto.CryptoLib

open FStar.HyperStack
open FStar.HyperStack.ST

let ctx_len = 1
let send_ctx : lbytes ctx_len = Seq.createL [0uy]
let recv_ctx : lbytes ctx_len = Seq.createL [1uy]

noeq type state =
     | S0 : my_sk:sig_key ->
	    their_vk:sig_verif_key ->
	    state
     | S1 : my_priv:dh_priv -> 
	    their_vk:sig_verif_key ->
	    state
     | S2 : #pub1:dh_pub ->
	    #pub2:dh_pub -> 
            send_key:ae_key pub1 pub2 1 send_ctx -> 
	    recv_key:ae_key pub1 pub2 1 recv_ctx -> 
	    send_counter:size_nat -> 
	    recv_counter:size_nat -> 
	    state
     | Stop: state


let init (my_sk:sig_key) (their_vk:sig_verif_key) =
    S0 my_sk their_vk

let signed_dh_send (st:state{S0? st}) = 
  let S0 sk vk = st in
  let priv = dh_keygen () in
  let pub = dh_priv_to_pub priv in
  let sv = sig_sign #dh_len sk pub in
  (pub, sv, S1 priv vk)

let signed_dh_recv (st:state{S1? st}) (their_pub:dh_pub) (sv:sig_sigval) = 
  let S1 my_priv vk = st in
  if sig_verify vk their_pub sv = true then
    let my_pub = dh_priv_to_pub my_priv in
    let sh = dh_shared my_priv their_pub in
    let send_k = kdf_derive sh send_ctx in
    let recv_k = kdf_derive sh recv_ctx in
    S2 send_k recv_k 0 0
  else Stop 

let msg_send (#my_vk:sig_verif_key)
             (#their_vk:sig_verif_key)
	     (#len:size_nat) 
	     (#pred:lbytes len -> Type0)
	     (st:state{S2? st}) 
	     (msg:ae_msg my_vk their_vk 1 send_ctx len pred) =
  let S2 send_k recv_k ctr1 ctr2 = st in
  if ctr1 + 1 < pow2 32 then 
    let n = random_bytes ae_nonce_len in
    let (c,t) = ae_enc send_k n ctr1 msg in
    Some (n,c,t,S2 send_k recv_k (ctr1 + 1) ctr2) 
  else None

let msg_recv (#my_vk:sig_verif_key)
             (#their_vk:sig_verif_key)
	     (#len:size_nat) 
	     (#pred:lbytes len -> Type0)
	     (st:state{S2? st}) 
	     (n:ae_nonce)
	     (cipher:lbytes len)
	     (tag:ae_tag) =
  let S2 #pub1 #pub2 send_k recv_k ctr1 ctr2 = st in
  if ctr2 + 1 < pow2 32 then 
    match ae_dec #my_vk #their_vk #pub1 #pub2 #1 #recv_ctx #len #pred
	  recv_k n ctr2 cipher tag with
    | Some msg ->  Some (msg, S2 send_k recv_k ctr1 (ctr2 + 1))
    | None -> None
  else None
  

