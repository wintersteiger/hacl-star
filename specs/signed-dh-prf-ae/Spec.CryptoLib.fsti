module Spec.CryptoLib

open FStar.Seq

type bytes = seq FStar.UInt8.t
type size_nat = n:nat{n < pow2 32}
type lbytes (n:size_nat) = b:bytes{length b = n}

(* Random Values *)

val entropy: Type0 // typically a secret key or a large number of pre-sampled bits
val random_bytes: e:entropy -> len:size_nat -> (lbytes len * entropy)

(* DH functionality *)
val dh_len : n:size_nat{n < pow2 20}
val dh_valid_pub: lbytes dh_len -> Type0
let dh_pub = b:lbytes dh_len{dh_valid_pub b} // sometimes, elements have a larger size
let dh_priv = lbytes dh_len
let dh_secret = lbytes dh_len

//val dh_keygen: entropy -> dh_priv * entropy
let dh_keygen e = random_bytes e dh_len
val dh_priv_to_pub: dh_priv -> dh_pub
val dh_shared: my_priv:dh_priv -> their_pub:dh_pub -> dh_secret

(* The following lemmas are derived from mathematical properties of 
   DH groups; they do not rely on any computational assumption or cryptographic game *)
val dh_pub_to_priv: p:dh_pub -> GTot (option dh_priv)

val dh_pub_inv: priv:dh_priv -> Lemma
			   (requires True)
			   (ensures (dh_pub_to_priv (dh_priv_to_pub priv) == Some priv))

val dh_shared_commutative: priv1:dh_priv -> priv2:dh_priv -> Lemma
			   (requires True)
			   (ensures (dh_shared priv1 (dh_priv_to_pub priv2) == 
				     dh_shared priv2 (dh_priv_to_pub priv1)))
val dh_shared_disjoint: priv1:dh_priv -> pub1:dh_pub -> pub2:dh_pub -> Lemma
			   (requires (pub1 <> pub2))
			   (ensures (dh_shared priv1 pub1 <>
				     dh_shared priv1 pub2))


(* KDF functionality *)

val kdf_derive: #klen:size_nat -> #clen:size_nat -> 
		k:lbytes klen ->  context:lbytes clen -> 
		olen:size_nat -> output:lbytes olen

(* Signature Functionality *)

val sig_key_size: size_nat
let sig_key = lbytes sig_key_size
let sig_verif_key = lbytes sig_key_size

val sig_size: size_nat
let sig_sigval = lbytes sig_size

val sig_keygen: entropy -> sig_key * entropy
val sig_priv_to_pub: sig_key -> sig_verif_key
val sig_sign: #len:size_nat -> k:sig_key -> msg:lbytes len -> sig_sigval
val sig_verify: #len:size_nat -> k:sig_verif_key -> msg:lbytes len -> sv:sig_sigval -> b:bool

(* Verify is an inverse of signature: mathematicel property *)
val sig_pub_to_priv: p:sig_verif_key -> GTot (s:sig_key{sig_priv_to_pub s == p})
val sig_sign_verify: #len:size_nat -> k:sig_key -> msg:lbytes len -> Lemma
		     (requires True)
		     (ensures (sig_verify #len (sig_priv_to_pub k) msg 
			      (sig_sign #len k msg) == true))

(* AE functionality *)

val ae_tag_len: size_nat
type ae_tag = lbytes ae_tag_len

val ae_nonce_len: size_nat
type ae_nonce = lbytes ae_nonce_len

val ae_key_len: size_nat
type ae_key = lbytes ae_key_len

val ae_enc: #len:size_nat -> k:ae_key -> n:ae_nonce -> ctr:size_nat -> 
	    msg:lbytes len -> (lbytes len * ae_tag)

val ae_dec: #len:size_nat -> k:ae_key -> n:ae_nonce -> ctr:size_nat ->
	    cipher:lbytes len -> tag:ae_tag -> option (lbytes len)

(* Dec is an inverse of Enc: mathematical property *)
val ae_enc_dec: #len:size_nat -> k:ae_key -> n:ae_nonce -> ctr:size_nat -> 
		msg:lbytes len -> Lemma
		(requires True)
		(ensures (let (c,t) = ae_enc #len k n ctr msg in
			  ae_dec #len k n ctr c t == Some msg))
