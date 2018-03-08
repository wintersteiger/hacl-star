module Spec.SignedDHAE

open FStar.Seq
open Spec.CryptoLib


(* PROTOCOL: signed-dh-ae *)
noeq 
type state = | S0 : e:entropy -> my_sk:sig_key -> their_vk:sig_verif_key -> state
	    | S1 : e:entropy -> priv:dh_priv -> their_vk:sig_verif_key -> state
	    | S2 : e:entropy -> send_key:ae_key -> recv_key:ae_key -> send_counter:size_nat -> recv_counter:size_nat -> state
	    | Stop: e:entropy -> state

let init (e:entropy) (my_sk:sig_key) (their_vk:sig_verif_key) : state = 
  S0 e my_sk their_vk
  
let signed_dh_send (st:state{S0? st}) : (dh_pub * sig_sigval * state) = 
  let S0 e sk vk = st in
  let priv,e = dh_keygen e in
  let pub = dh_priv_to_pub priv in
  let sv = sig_sign #dh_len sk pub in
  (pub, sv, S1 e priv vk)

let signed_dh_recv (st:state{S1? st}) (their_pub:dh_pub) (sv:sig_sigval) : state = 
  let S1 e my_priv vk = st in
  if sig_verify #dh_len vk their_pub sv = true then
    let my_pub = dh_priv_to_pub my_priv in
    let sh = dh_shared my_priv their_pub in
    let clen : size_nat = 1 + dh_len + dh_len in
    let ctx1 = createL [0uy] @| my_pub @| their_pub in
    let ctx2 = createL [1uy] @| their_pub @| my_pub in
    let send_k = kdf_derive #dh_len #clen sh ctx1 ae_key_len in
    let recv_k = kdf_derive #dh_len #clen sh ctx2 ae_key_len in
    S2 e send_k recv_k 0 0
  else Stop e

let msg_send (#len:size_nat) (st:state{S2? st}) (msg:lbytes len) : option (ae_nonce * lbytes len * ae_tag * state) = 
  let S2 e send_k recv_k ctr1 ctr2 = st in
  if ctr1 + 1 < pow2 32 then 
    let n,e = random_bytes e ae_nonce_len in
    let (c,t) = ae_enc #len send_k n ctr1 msg in
    Some (n,c,t,S2 e send_k recv_k (ctr1 + 1) ctr2) 
  else None

let msg_recv (#len:size_nat) (st:state{S2? st}) (n:ae_nonce) (cipher:lbytes len) (tag:ae_tag) : option (lbytes len * state) = 
  let S2 e send_k recv_k ctr1 ctr2 = st in
  if ctr2 + 1 < pow2 32 then 
    match ae_dec #len recv_k n ctr2 cipher tag with
    | Some msg ->  Some (msg, S2 e send_k recv_k ctr1 (ctr2 + 1))
    | None -> None
  else None
  
  

