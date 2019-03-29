module Spec.Signal.Crypto

open FStar.Mul
open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Spec.Old.Ed25519

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* BB. Relocate to Spec.Signal.Constants ? *)
inline_for_extraction let size_privkey = 32
inline_for_extraction let size_pubkey = 33
inline_for_extraction let size_key = 32
inline_for_extraction let size_iv = 16
inline_for_extraction let size_tag = 32
inline_for_extraction let size_sigval = 64
let cipherlen (plen:size_nat{plen + 16 <= max_size_t}) : size_nat =
  ((plen + 16) / 16) `op_Multiply` 16

type privkey = lbytes size_privkey
type pubkey = lbytes size_pubkey
type key = lbytes size_key
type iv = lbytes size_iv
type tag = lbytes size_tag
type sigval = lbytes size_sigval

(* BB. Relocate to Spec.Signal.Constants ? *)
let pow2_61 : l:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)

(* BB. Relocate to Spec.Signal.Constants ? *)
let ff1 : lbytes 1 = create 1 (u8 0xFF)

let lbytes_sub (x:size_nat) = b:bytes{length b <= x}


let to_evercrypt_seq (#len:size_nat) (s: lseq uint8 len) =
  Lib.Sequence.map (fun v -> FStar.UInt8.uint_to_t (Lib.IntTypes.v v)) s

let from_evercrypt_seq (#len:size_nat) (s: Spec.Hash.Definitions.lbytes len) : lseq uint8 len =
  Lib.Sequence.map (fun v -> Lib.IntTypes.u8 (FStar.UInt8.v v)) (to_lseq s)

inline_for_extraction
let basepoint_list : x:list byte_t{List.Tot.length x == 32} =
  [@inline_let]
  let l =
    [9uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] in
  assert_norm (List.Tot.length l == 32);
  l

let basepoint_lseq : Lib.Sequence.lseq byte_t 32 =
  Lib.Sequence.of_list basepoint_list

val priv_to_pub: our_priv_key:privkey -> our_pub_key:pubkey
let priv_to_pub kpriv =
  let raw_pub_key = Spec.Old.Curve25519.scalarmult (to_evercrypt_seq kpriv) basepoint_lseq in
  ff1 @| (from_evercrypt_seq #32 raw_pub_key)

val dh: our_priv_key:privkey -> their_pub_key:pubkey -> shared_secret:key
let dh kpriv kpub =
  let raw_kpub = sub kpub 1 32 in
  from_evercrypt_seq (Spec.Old.Curve25519.scalarmult
    (to_evercrypt_seq kpriv) (to_evercrypt_seq raw_kpub)
  )

val hkdf1: key:lbytes_sub 160 -> salt:lbytes 32 -> info:lbytes_sub 32  -> lbytes 32
let hkdf1 key salt info =
  let extracted = EverCrypt.HKDF.extract Spec.Hash.Definitions.SHA2_256
    (to_evercrypt_seq salt)
    (to_evercrypt_seq #(length key) key)
  in from_evercrypt_seq (
    EverCrypt.HKDF.expand Spec.Hash.Definitions.SHA2_256 extracted
      (to_evercrypt_seq #(length info) info) 32
  )

val hkdf2: key:lbytes 32 -> salt:lbytes 32 -> info:lbytes_sub 32 -> lbytes 64
let hkdf2 key salt info =
  let extracted = EverCrypt.HKDF.extract Spec.Hash.Definitions.SHA2_256
    (to_evercrypt_seq salt)
    (to_evercrypt_seq key)
  in from_evercrypt_seq (
    EverCrypt.HKDF.expand Spec.Hash.Definitions.SHA2_256 extracted
      (to_evercrypt_seq #(length info) info) 64
  )

val hkdf3: key:lbytes 32 -> salt:lbytes 32 -> info:lbytes_sub 32 -> lbytes 96
let hkdf3 key salt info =
  let extracted = EverCrypt.HKDF.extract Spec.Hash.Definitions.SHA2_256
    (to_evercrypt_seq salt)
    (to_evercrypt_seq key)
  in
   from_evercrypt_seq (
    EverCrypt.HKDF.expand Spec.Hash.Definitions.SHA2_256 extracted
      (to_evercrypt_seq #(length info) info) 96
  )

val aes_enc:
  ek:key ->
  iv:iv ->
  plain:bytes{length plain + Spec.AES256.blocklen <= max_size_t}  ->
  Tot (cipher:bytes{length cipher <= length plain + 16})
let aes_enc ek iv plain =
   Spec.AES256_CBC.aes256_cbc_encrypt ek iv plain (length plain)


val aes_dec:
  ek:key ->
  iv:iv ->
  cipher:bytes{
    length cipher % 16 == 0 /\ length cipher > 0 /\
    length cipher <= max_size_t
  } ->
  Tot (option (plain:bytes{
    length plain + 16 <= max_size_t /\
    cipherlen (length plain) = length cipher
  }))
let aes_dec ek iv cipher =
  Spec.AES256_CBC.aes256_cbc_decrypt ek iv cipher (length cipher)

val hmac:
    key:key
    -> input: bytes{length input <= max_size_t} ->
  Tot (lbytes 32)
let hmac mk plain =
  assert_norm(max_size_t <= pow2 61 - 1 - size_key - 64);
  from_evercrypt_seq (EverCrypt.HMAC.hmac Spec.Hash.Definitions.SHA2_256
    (to_evercrypt_seq mk)
    (to_evercrypt_seq #(length plain) plain)
  )


val sign: sk:privkey -> plain:bytes{8 * length plain < max_size_t} -> sv:sigval
let sign sk plain =
  Spec.Old.Ed25519.sign sk plain


val verify: pk:pubkey -> plain:bytes{8 * length plain < max_size_t} -> sv:sigval -> bool
let verify pk plain sv =
  let raw_pk = sub pk 1 32 in
  Spec.Old.Ed25519.verify raw_pk plain sv
