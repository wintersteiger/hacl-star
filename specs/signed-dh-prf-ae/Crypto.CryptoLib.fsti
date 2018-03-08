module Crypto.CryptoLib

module Spec = Spec.CryptoLib
open Spec.CryptoLib

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Monotonic.RRef

(* LOGS and LOG PREDICATES *)
(* The only state in our memory model is a set of global, eternal
   logs.  We declare them as top-level global constants in modules, we
   assume that they are eternal and that they only grow over time,
   i.e.  all changes to the heap preserve table liveness and log
   contents.  We ignore liveness in our types and only track log
   extensions.

   In the cryptographic model, only honest instances are allowed to
   write and read the log *)

val log: event:Type -> Type0
val logged: log 'event -> (e:'event -> Type0) -> mem -> Type0
val extends0: mem -> mem -> Type0
val extends1: log 'event -> mem -> mem -> Type0
val extends2: log 'event1 -> log 'event2 -> mem -> mem -> Type0
val extends3: log 'event1 -> log 'event2 -> log 'event3 -> mem -> mem -> Type0
// Monotonic predicates over the logs
val monotonic: (mem -> Type0) -> Type0
let log_pred = p:(mem -> Type0){monotonic p}

(* monotonic p ==> (forall h0 h1. (p h0 /\ extends0 h0 h1 ==> p h1)) /\
		(forall e1 l1 h0 h1. (p h0 /\ extends1 #e1 l1 h0 h1 ==> p h1)) /\
		(forall e1 e2 l1 l2 h0 h1. (p h0 /\ extends2 #e1 #e2 l1 l2 h0 h1 ==> p h1)) /\
		(forall e1 e2 e3 l1 l2 l3 h0 h1. (p h0 /\ extends3 #e1 #e2 #e3 l1 l2 l3 h0 h1 ==> p h1)) 
*)

(* BYTESTRINGS and LARGE, RANDOM values *)
(* The crypto library manipulates bytestrings (and subtypes) of a certain length
           lbytes (len:size_nat)
           rbytes (len:size_nat) (p:lbytes len -> Type0)
   We can generate random bytes of these types.
   We identify "large" subtypes of bytestrings with the following predicate:
            large (len:size_nat) (ty:lbytes len -> Type0)

   This predicate means that the subtype has enough elements that
   secrets of this btype cannot be guessed by the adversary.
   
   For example, we may assume: 
            large 16 (fun x -> True)
   to state that 128-bit bitstrings are too large for the adversary to guess 
*)

let rbytes (len:size_nat) (p:lbytes len -> Type0) = b:lbytes len{p b}
val large: len:size_nat -> ty:(lbytes len -> Type0) -> Type0

(* Random Bytestrings *)
noeq type random_event = | REv: #len:size_nat -> entropy -> lbytes len -> random_event
val random_log: log random_event

let honest_random (#len:size_nat) (rand:lbytes len) (m:mem) = 
    logged random_log (fun (REv e r) -> r == rand) m
    
val random_bytes: len:size_nat -> ST (lbytes len)
			       (requires (fun h -> True))
			       (ensures (fun h0 b h1 -> 
					 extends1 random_log h0 h1 /\
					 honest_random #len b h1))

(* SECRET BYTESTRINGS *)
(* A distinguished class of subtypes is secret bytestrings,
 represented as an abstract parameterized type where the parameters
 contain all the publicly known information about the secret:

   secret index content_len content_pred usage auth_inv leak_cond

 where:
      index is a value that indicates the "session" in which this secret is used
      content_len   is the length of the content bytestring
      content_pred  identifies the subtype of "lbytes len" that the content is in
      usage restricts the crypto-library usage of the secret
      auth_inv is a monotonic log predicate that held in the heap where the secre was created
      leak_cond is a monotonic log predicate under which the value is no longer secret
 Note: we can consolidate all these parameters into a single "index" type, and
 compute all other parameters using global functions, but here, we have left
 the parameters explicit for simplicity.

 For keys, we use "large" secrets, i.e. "large content_len content_pred"
 For plaintexts, we can use "small" secrets, i.e. any secret type that has >= 2 values, e.g. content_len = 1 or content_pred = (fun b -> b = yes \/ b = no)

 Cryptographically:
 (a) elements of type "secret i l p u a c" are indistinguishable 
     from random values of type "rbytes l p" in any state where c does not hold.
 (b) secrets with different indexes are indistinguishable from 
 independently random values in any heap where their leak conditions do not hold
 (c) each secret is a witness to the heap in which it was constructed, and hence can be used to prove the auth_inv in the current heap
*)

(* USAGES *)
(* We hardcode a set of usages supported by this library.  For each
   secret, its usage must be chosen at generation/computation time,
   but never changed.  
   
   The crypto assumptions in this file only hold if each secret is
   used only in accordance with its specified usage: e.g. if a AE_KEY
   is used as a KDF_KEY in some other module, all bets are off. *)

type usage = | AE_KEY | AE_MSG | DH_PRIV | SIG_KEY | KDF_KEY 
val secret: #index_ty:Type0 ->
	    index: index_ty ->
	    content_len:size_nat ->
	    content_pred:(lbytes content_len -> Type0) -> 
	    usage:usage -> 
	    auth_inv:log_pred ->
	    leak_cond:log_pred ->
	    Type0

val secret_v: #ty:Type0 -> #i:ty -> #u:usage -> #len:size_nat -> #p:(lbytes len -> Type0) -> #a:log_pred -> #c:log_pred -> s:secret i len p u a c -> GTot (rbytes len p)
val secret_leak: #ty:Type0 -> #i:ty -> #u:usage -> #len:size_nat -> #p:(lbytes len -> Type0) -> #a:log_pred -> #c:log_pred -> s:secret i len p u a c -> 
		 ST (rbytes len p)
		  (requires (fun h -> c h))
		  (ensures (fun h r h' -> r == secret_v s))

val auth_witness: #ty:Type0 -> #i:ty -> #u:usage -> #len:size_nat -> #p:(lbytes len -> Type0) -> #a:log_pred -> #c:log_pred -> s:secret i len p u a c -> 
		 ST unit
		  (requires (fun h -> True))
		  (ensures (fun h r h' -> a h'))
		  
(* Computational Diffie-Hellman Assumption for DH: 
   A DH computation between honest public keys results in a large shared secret *)

// Private keys are uncondonitionally secret (no dynamic compromise)
let dh_priv = 
    secret 
    ()
    Spec.dh_len 
    (fun b -> True) 
    DH_PRIV     
    (fun m -> True)
    (fun m -> True)

let dh_pub = Spec.dh_pub
let dh_elem : ty:(lbytes Spec.dh_len -> Type0){large Spec.dh_len ty} = 
	      assume (large Spec.dh_len Spec.dh_valid_pub);
	      Spec.dh_valid_pub

// DH key generation
val dh_gen_log: log dh_pub
let honest_dh_pub (pub:dh_pub) (m:mem) = 
    logged dh_gen_log (fun p -> p == pub) m
val dh_keygen: unit -> ST (dh_priv)
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> 
				 extends2 random_log dh_gen_log h0 h1 /\
				 honest_dh_pub (Spec.dh_priv_to_pub (secret_v b)) h1))
val dh_priv_to_pub: priv:dh_priv -> pub:dh_pub{pub == Spec.dh_priv_to_pub (secret_v priv)}

let dh_cond pub1 pub2 : log_pred = 
  let p = (fun m -> ~ (honest_dh_pub pub1 m) \/ ~ (honest_dh_pub pub2 m)) in
  assume (monotonic p);
  p
  
// DH shared secret.
// The CDH assumption is parameteric over the index, usage, leak condition of
// the shared secret
// In this Library, we specialize its usage to only be used as a KDF_KEY

let dh_secret (pub1:dh_pub) (pub2:dh_pub) = 
    secret 
    (pub1, pub2)
    dh_len
    dh_elem   
    KDF_KEY
    (fun m -> True)
    (dh_cond pub1 pub2)

// DH computation
noeq type dh_event = | DHEv: pub1:dh_pub -> pub2:dh_pub -> dh_secret pub1 pub2 -> dh_event
val dh_secret_log: log dh_event

// The following function must not be called twice with the same keys but different usages, otherwise the CDH assumption would fail.
val dh_shared: my_priv:dh_priv -> their_pub:dh_pub -> ST (dh_secret (dh_priv_to_pub my_priv) their_pub)
			(requires (fun h -> True))
			(ensures (fun h0 r h1 -> 
				 secret_v r == Spec.dh_shared (secret_v my_priv) their_pub /\
				 extends1 dh_secret_log h0 h1 /\
				 logged dh_secret_log 
				  (fun (DHEv p1 p2 s) -> 
					p1 == dh_priv_to_pub my_priv /\
					p2 == their_pub /\
					s == r) h1))
       
(* Random Oracle Assumption for KDF *)
(* kdf_derive takes a *large* secret and generates a uniformly random *large* secret bytestring *)

(* The RO assumption is parameteric over the parameters of the input and output secrets *)
(* In this library, we specialize its input to be a dh_secret and its output to be an AE_KEY *)

let kdf_key (pub1:dh_pub) (pub2:dh_pub) = 
    dh_secret pub1 pub2 
    
let kdf_secret (pub1:dh_pub) (pub2:dh_pub) (clen:size_nat) (context:lbytes clen) = 
    secret 
    (pub1, pub2, context)
    Spec.ae_key_len
    (fun _ -> True)
    AE_KEY
    (fun m -> True)
    (dh_cond pub1 pub2)
    
val kdf_derive: #pub1:dh_pub ->
		#pub2:dh_pub ->
		#clen:size_nat -> 
		k:kdf_key pub1 pub2 ->
		context:lbytes clen ->
		ST (kdf_secret pub1 pub2 clen context)
		(requires (fun h0 -> True))
		(ensures (fun h0 o h1 -> 
		   secret_v o == Spec.kdf_derive (secret_v k) context Spec.ae_key_len))
		
(* UF-CMA Assumption for Signature *)

(* The assumption is parameteric over the signature predicate.
   Here, we specialize it to sign honest DH public keys *)
let sig_pred_ty = #len:size_nat -> lbytes len -> log_pred 
let sig_pred : sig_pred_ty = 
    (fun #len b -> 
      let p = (fun m -> len == Spec.dh_len /\ dh_elem b /\
		     honest_dh_pub b m) in
      assume (monotonic p);
      p)
    
let sig_key = 
    secret 
    ()
    Spec.sig_key_size 
    (fun b -> True) 
    SIG_KEY
    (fun m -> True)
    (fun m -> True)
    
let sig_verif_key =  Spec.sig_verif_key

let sig_sigval = Spec.sig_sigval


// SIG key generation
noeq type sig_gen_event = | SigGenEv: pub:sig_verif_key -> sig_gen_event

val sig_gen_log: log sig_gen_event
let honest_sig_verif_key (pub:Spec.sig_verif_key) (m:mem) = 
    logged sig_gen_log (fun (SigGenEv p) -> p == pub) m

val sig_keygen: unit -> ST (sig_key)
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> 
				 extends2 random_log sig_gen_log h0 h1 /\
				 honest_sig_verif_key (Spec.sig_priv_to_pub (secret_v b)) h1))
val sig_priv_to_pub:  priv:sig_key -> pub:sig_verif_key {pub == Spec.sig_priv_to_pub (secret_v priv)}

// Signing and Verification
noeq type sign_event = | SignEv: #len:size_nat -> 
			    pub:sig_verif_key -> 
			    msg:lbytes len ->
			    tag:sig_sigval -> 
			    sign_event
			    
val sig_sign_log: log sign_event

val sig_sign: #len:size_nat -> 
	      k:sig_key -> 
	      msg:lbytes len -> 
	      ST sig_sigval
	      (requires (fun h -> sig_pred #len msg h))
	      (ensures (fun h0 sv h1 ->
	    	        sv == Spec.sig_sign #len (secret_v k) msg /\
			extends1 sig_sign_log h0 h1 /\
			logged sig_sign_log 
			      (fun (SignEv pub' msg' sv') -> 
				  pub' == (sig_priv_to_pub k) /\
				  msg' == msg /\
				  sv' == sv) h1))

val sig_verify: #len:size_nat -> 
		k:sig_verif_key -> 
		msg:lbytes len -> 
		sv:sig_sigval -> 
		ST bool
		(requires (fun h -> True))
		(ensures (fun h0 r h1 ->
		     r == Spec.sig_verify #len k msg sv /\
		     ((r == true /\
		       honest_sig_verif_key k h0) ==>
		        sig_pred #len msg h1 /\
			logged sig_sign_log 
			  (fun (SignEv pub' msg' sv') ->
			     pub' == k /\
			     msg' == msg) h0)))

(* If we use SUF-CMA instead of UF-CMA, we also have that the signature value 
   sent by the signer is the same as the value used by the receiver *)


(* IND-CCA for Probabilistic Authenticated Encryption *)
(* The assumption is parameteric over the input secret and key parameters.
   Here we specialize it for use with signed DH params *)

let key_cond (pub1:dh_pub) (pub2:dh_pub) = 
    dh_cond pub1 pub2 
let ae_key (pub1:dh_pub) (pub2:dh_pub) (clen:size_nat) (context:lbytes clen) = 
    kdf_secret pub1 pub2 clen context

let msg_cond (my_vk:sig_verif_key) 
  	     (their_vk:sig_verif_key) = 
    let p =  (fun m -> honest_sig_verif_key my_vk m /\
		    honest_sig_verif_key their_vk m) in
    assume (monotonic p);
    p
	    
let ae_msg (my_vk:sig_verif_key) 
	   (their_vk:sig_verif_key)
	   (clen:size_nat) 
	   (context:lbytes clen) 
	   (len:size_nat) 
	   (pred:lbytes len -> Type0) =
    secret
    (my_vk, their_vk, context)
    len
    pred
    AE_MSG
    (fun m -> True)
    (msg_cond my_vk their_vk)

let ae_nonce = Spec.ae_nonce
let ae_tag = Spec.ae_tag

noeq type ae_event = | AEEv: #my_vk:sig_verif_key ->
			     #their_vk:sig_verif_key ->
			     #pub1:dh_pub ->
			     #pub2:dh_pub ->
			     #clen:size_nat ->
			     #context: lbytes clen ->
			     #len:size_nat -> 
			     #pred:(lbytes len -> Type0) ->
			     k:ae_key pub1 pub2 clen context ->
			     msg:ae_msg my_vk their_vk clen context len pred ->
			     cipher: lbytes len ->
			     tag:ae_tag ->
			     ae_event
			
val ae_log: log ae_event

val ae_enc: #my_vk:sig_verif_key ->
            #their_vk:sig_verif_key ->
            #pub1:dh_pub ->
	    #pub2:dh_pub ->
	    #clen:size_nat ->
	    #context: lbytes clen ->
	    #len:size_nat -> 
	    #pred:(lbytes len -> Type0) ->
	    k:ae_key pub1 pub2 clen context -> 
	    n:ae_nonce -> 
	    ctr:size_nat -> 
	    msg:ae_msg my_vk their_vk clen context len pred ->
	    ST (lbytes len * ae_tag)
	    (requires (fun h -> key_cond pub1 pub2 h ==>
			     msg_cond my_vk their_vk h))
	    (ensures (fun h0 (e,t) h1 ->
			(e,t) == Spec.ae_enc (secret_v k) n ctr (secret_v msg) /\
			extends1 ae_log h0 h1 /\
			logged ae_log 
			 (fun (AEEv k' msg' e' t') ->
			  k' == k /\
			  secret_v msg' == (secret_v msg) /\
			  e' == e /\
			  t' == t) h1))

val ae_dec: #my_vk:sig_verif_key ->
            #their_vk:sig_verif_key ->
	    #pub1:dh_pub ->
	    #pub2:dh_pub ->
	    #clen:size_nat ->
	    #context: lbytes clen ->
	    #len:size_nat -> 
	    #pred:(lbytes len -> Type0) ->
	    k:ae_key pub1 pub2 clen context -> 
	    n:ae_nonce -> 
	    ctr:size_nat -> 
	    cipher: lbytes len ->
	    tag: ae_tag ->
	    ST (option (ae_msg my_vk their_vk clen context len pred))
	    (requires (fun h -> key_cond pub1 pub2 h ==> 
			     msg_cond my_vk their_vk h))
	    (ensures (fun h0 msg h1 ->
		      match msg with
		      | Some m -> 
			     Some (secret_v m) == Spec.ae_dec (secret_v k) n ctr cipher tag /\
			     logged ae_log 
			       (fun (AEEv k' msg' e' t') -> 
				  k' == k /\
				  secret_v msg' == secret_v m /\
				  e' == cipher /\
				  t' == tag) h0 
		      | None -> True))




