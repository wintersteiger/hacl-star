module Impl.Signal.Crypto

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"

val const_ff1: b:ilbuffer uint8 (size 1){
  recallable b /\ witnessed b Spec.Signal.Messages.ff1
}
let const_ff1 = createL_global Spec.Signal.Messages.ff1_list

/// Type definitions

type privkey_p = lbuffer uint8 (size Spec.Signal.Crypto.size_privkey)
type pubkey_p = lbuffer uint8 (size Spec.Signal.Crypto.size_pubkey)
type key_p = lbuffer uint8 (size Spec.Signal.Crypto.size_key)
type sigval_p = lbuffer uint8 (size Spec.Signal.Crypto.size_sigval)

(* Lib.ByteBuffer lbytes equal *)
assume val secure_compare:
    #vlen: Ghost.erased size_nat
  -> len: size_t{size_v len == Ghost.reveal vlen}
  -> input0: lbuffer uint8 len
  -> input1: lbuffer uint8 len ->
  Stack bool
	 (requires (fun h -> live h input0 /\ live h input1))
	 (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
	   b = Lib.Sequence.for_all2 (fun (x:uint8) (y:uint8) ->
	     Lib.RawIntTypes.(u8_to_UInt8 x = u8_to_UInt8 y
	   )) (as_seq h0 input0) (as_seq h0 input1)
	 ))

#set-options "--admit_smt_queries true"

(*let secure_compare #vlen len input0 input1 =
 Lib.ByteBuffer.lbytes_eq #len input0 input1
*)
#set-options "--admit_smt_queries false"

val priv_to_pub:
    output: lbuffer uint8 (size 33)
  -> secret: lbuffer uint8 (size 32) ->
  Stack unit
	 (requires (fun h -> live h output /\ live h secret /\ disjoint output secret))
	 (ensures (fun h0 _ h1 -> modifies1 output h0 h1 /\
	   as_seq h1 output == Spec.Signal.Crypto.priv_to_pub (as_seq h0 secret)
	 ))

#set-options "--admit_smt_queries true"

let priv_to_pub output secret =
  let pub = sub output (size 1) (size 32) in
  Hacl.Curve25519_51.secret_to_public pub secret;
  update_sub output (size 0) (size 1) const_ff1

#set-options "--admit_smt_queries false"

(* Curve, _dev_combinators *)
val dh:
    output: lbuffer uint8 (size 32)
  -> secret: lbuffer uint8 (size 32)
  -> public: lbuffer uint8 (size 33) ->
  Stack unit
	 (requires (fun h -> live h output /\ live h secret /\ live h public /\ disjoint output secret))
	 (ensures (fun h0 _ h1 -> modifies1 output h0 h1 /\
	   as_seq h1 output == Spec.Signal.Crypto.dh (as_seq h0 secret) (as_seq h0 public)
	 ))
#set-options "--admit_smt_queries true"

let dh output secret public =
  Hacl.Curve25519_51.ecdh output secret public

#set-options "--admit_smt_queries false"


(* Demander à Jonathan ou bien code/experimental dans _dev *)
assume val hkdf1:
     #vlen: (Ghost.erased size_nat){Ghost.reveal vlen <= 160}
  -> #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output:lbuffer uint8 (size 32)
  -> len  :size_t{v len = Ghost.reveal vlen}
  -> input:lbuffer uint8 len
  -> salt:ilbuffer uint8 (size 32)
  -> ilen  :size_t{v ilen = Ghost.reveal vilen}
  -> info:ilbuffer uint8 ilen  ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input /\ disjoint output salt /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf1
	    (as_seq h0 input) (as_seq h0 salt) (as_seq h0 info)
	))

assume val hkdf2:
    #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output: lbuffer uint8 (size 64)
  -> input: lbuffer uint8 (size 32)
  -> salt: lbuffer uint8 (size 32)
  -> ilen: size_t{v ilen = Ghost.reveal vilen}
  -> info: ilbuffer uint8 ilen ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input
                         /\ disjoint output salt
                         /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf2
	    (as_seq h0 input) (as_seq h0 salt) (as_seq h0 info)
	))

assume val hkdf3:
     #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output:lbuffer uint8 (size 96)
  -> input:lbuffer uint8 (size 32)
  -> salt: ilbuffer uint8 (size 32)
  -> ilen:size_t{v ilen = Ghost.reveal vilen}
  -> info: ilbuffer uint8 ilen ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input
                         /\ disjoint output salt
                         /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf3
	    (as_seq h0 input)  (as_seq h0 salt) (as_seq h0 info)
	))

(* _dev_wasm *)
assume val enc:
     #vlen: (Ghost.erased size_nat){
       Ghost.reveal vlen + 16 <= max_size_t /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal vlen) + 140 <= max_size_t
     }
  -> len: size_t{size_v len = Ghost.reveal vlen}
  -> ciphertext: lbuffer uint8 (len +! size 16)
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> plaintext: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint ciphertext key
                     /\ disjoint ciphertext iv
                     /\ disjoint ciphertext plaintext))
    (ensures  (fun h0 _ h1 -> modifies1 ciphertext h0 h1 /\
      Seq.sub (as_seq h1 ciphertext) 0 (Spec.Signal.Crypto.cipherlen (Ghost.reveal vlen)) ==
	Spec.Signal.Crypto.aes_enc (as_seq h0 key) (as_seq h0 iv) (as_seq h0 plaintext)
    ))

assume val dec:
    #vlen: (Ghost.erased size_nat){Ghost.reveal vlen % 16 = 0 /\ Ghost.reveal vlen > 0}
  -> len: size_t{size_v len = Ghost.reveal vlen}
  -> plaintext: lbuffer uint8 len
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> ciphertext: lbuffer uint8 len ->
  Stack size_t
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint plaintext key
                     /\ disjoint plaintext iv
                     /\ disjoint plaintext ciphertext))
    (ensures  (fun h0 plainlen h1 -> modifies1 plaintext h0 h1 /\
      begin if v plainlen <> 0 then
	v plainlen + 16 <= max_size_t /\
	Spec.Signal.Crypto.cipherlen (v plainlen) == Ghost.reveal vlen /\
	Some(Seq.sub (as_seq h1 plaintext) 0 (v plainlen)) == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      else
	None == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      end
    ))

(* _dev/code/experimental/hmac *)
assume val hmac:
     #vdlen: Ghost.erased size_nat
  -> mac: lbuffer uint8 (size 32)
  -> key: lbuffer uint8 (size 32)
  -> dlen: size_t{v dlen = Ghost.reveal vdlen}
  -> data: ilbuffer uint8 dlen ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data
                       /\ disjoint mac key
                       /\ disjoint mac data))
        (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1 /\
	  as_seq h1 mac == Spec.Signal.Crypto.hmac (as_seq h0 key) (as_seq h0 data)
	))

(* Voir dans lib pour caster un immut vers un mut *)
assume val hmac_mut:
     #vdlen: Ghost.erased size_nat
  -> mac: lbuffer uint8 (size 32)
  -> key: lbuffer uint8 (size 32)
  -> dlen: size_t{v dlen = Ghost.reveal vdlen}
  -> data: lbuffer uint8 dlen ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data
                       /\ disjoint mac key
                       /\ disjoint mac data))
        (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1 /\
	  as_seq h1 mac == Spec.Signal.Crypto.hmac (as_seq h0 key) (as_seq h0 data)
	))

(* _dev_wasm *)
assume val sign:
    #vlen:(Ghost.erased size_nat){8 * Ghost.reveal vlen < max_size_t}
  -> sigval: lbuffer uint8 (size 64)
  -> secret: privkey_p
  -> len:size_t{v len = Ghost.reveal vlen}
  -> msg:lbuffer uint8 len ->
  Stack unit
	 (requires (fun h -> live h sigval /\ live h secret /\ live h msg
					      /\ disjoint sigval secret
					      /\ disjoint sigval msg))
	 (ensures (fun h0 _ h1 -> modifies1 sigval h0 h1 /\
	   as_seq h1 sigval == Spec.Signal.Crypto.sign (as_seq h0 secret) (as_seq h0 msg)
	 ))

(*_dev_wasm *)
assume val verify:
    #vlen: (Ghost.erased size_nat){8 * Ghost.reveal vlen < max_size_t}
  -> sigval: lbuffer uint8 (size 64)
  -> pub: pubkey_p
  -> len:size_t{size_v len = Ghost.reveal vlen}
  -> msg: lbuffer uint8 len->
  Stack bool
    (requires (fun h -> live h sigval /\ live h pub /\ live h msg))
    (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
       b == Spec.Signal.Crypto.verify
	 (as_seq h0 pub) (as_seq h0 msg) (as_seq h0 sigval)
    ))

let cipherlen (plen:size_t{v plen + 16 <= max_size_t})
  : Tot (r:size_t{v r = Spec.Signal.Crypto.cipherlen (v plen)}) =
  ((plen +. size 16) /. size 16) *. size 16
