module Spec.RSA

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.RawIntTypes

open Lib.Sequence
open Lib.ByteSequence

open Spec.Bignum.Basic
open Spec.RSA.Bignum

module Hash = Spec.SHA2

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let lbytes len = lseq uint8 len

val xor_bytes:
     #len:size_pos
  -> b1:lbytes len
  -> b2:lbytes len
  -> lbytes len
let xor_bytes #len b1 b2 =
  map2 (fun x y -> x ^. y) b1 b2

val eq_bytes:
    #len:size_nat
  -> b1:lbytes len
  -> b2:lbytes len
  -> bool
let eq_bytes #len b1 b2 = lbytes_eq b1 b2

(* SHA256 *)
let max_input_len_sha256 = pow2 61
let hLen = 32

val hash_sha256:
     #len:size_nat{len < max_input_len_sha256}
  -> msg:lbytes len
  -> lbytes hLen
let hash_sha256 #len msg =
  Hash.hash256 len msg

(* Mask Generation Function *)
(* max_size_t = pow2 32 - 1 *)
val mgf_sha256:
     #len:size_nat{len + 4 < max_size_t /\ len + 4 < max_input_len_sha256}
  -> mgfseed:lbytes len
  -> maskLen:size_pos{(blocks maskLen hLen) * hLen < pow2 32}
  -> lbytes maskLen
let mgf_sha256 #len mgfseed maskLen =
  let n = blocks maskLen hLen in
  let acc = create (n * hLen) (u8 0) in

  let mgfseed_counter = create (len + 4) (u8 0) in
  let mgfseed_counter = update_sub mgfseed_counter 0 len mgfseed in

  let acc =
    repeati n
    (fun i acc ->
      let counter = nat_to_bytes_be 4 i in
      let mgfseed_counter = update_sub mgfseed_counter len 4 counter in
      let mHash = hash_sha256 mgfseed_counter in
      update_sub acc (hLen * i) hLen mHash
    ) acc in
  sub acc 0 maskLen

(* RSA *)
type modBits = modBits:size_pos{64 <= modBits /\ 2 * 64 * (blocks modBits 64 + 1) < max_size_t /\
                                blocks (8 * blocks modBits 8) 8 < max_size_t}

noeq type rsa_pubkey (modBits:modBits) (eBits:size_pos) =
  | Mk_rsa_pubkey: n:bignum modBits{1 < bn_v n /\ pow2 (modBits - 1) <= bn_v n}
                -> e:bignum eBits{bn_v e < bn_v n}
                -> rsa_pubkey modBits eBits

noeq type rsa_privkey (modBits:modBits) (eBits:size_pos) (dBits:size_pos) (pBits:size_pos) (qBits:size_pos) =
  | Mk_rsa_privkey: pkey:rsa_pubkey modBits eBits
                 -> d:bignum dBits{0 < bn_v d /\ bn_v d < bn_v (Mk_rsa_pubkey?.n pkey)}
                 -> p:bignum pBits{1 < bn_v p /\ bn_v p < bn_v (Mk_rsa_pubkey?.n pkey) /\
                                   pBits + qBits + 65 < max_size_t /\ dBits < pBits + qBits + 64}
                 -> q:bignum qBits{1 < bn_v q /\ bn_v q < bn_v (Mk_rsa_pubkey?.n pkey) /\
                                   bn_v (Mk_rsa_pubkey?.n pkey) = bn_v p * bn_v q}
                 -> rsa_privkey modBits eBits dBits pBits qBits

val db_zero:
     #len:size_pos
  -> db:lbytes len
  -> emBits:size_nat
  -> lbytes len
let db_zero #len db emBits =
  let msBits = emBits % 8 in
  if msBits > 0 then
    db.[0] <- db.[0] &. (u8 0xff >>. u32 (8 - msBits))
  else db

val pss_encode:
     #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> salt:lbytes sLen
  -> msg:lbytes msgLen
  -> emBits:size_pos{hLen + sLen + 2 <= blocks emBits 8}
  -> lbytes (blocks emBits 8)
let pss_encode #sLen #msgLen salt msg emBits =
  let mHash = hash_sha256 msg in

  //m1 = [8 * 0x00; mHash; salt]
  let m1Len = 8 + hLen + sLen in
  let m1 = create m1Len (u8 0) in
  let m1 = update_sub m1 8 hLen mHash in
  let m1 = update_sub m1 (8 + hLen) sLen salt in
  let m1Hash = hash_sha256 m1 in

  //db = [0x00;..; 0x00; 0x01; salt]
  let emLen = blocks emBits 8 in
  let dbLen = emLen - hLen - 1 in
  let db = create dbLen (u8 0) in
  let last_before_salt = dbLen - sLen - 1 in
  let db = db.[last_before_salt] <- u8 1 in
  let db = update_sub db (last_before_salt + 1) sLen salt in

  let dbMask = mgf_sha256 m1Hash dbLen in
  let maskedDB = xor_bytes db dbMask in
  let maskedDB = db_zero maskedDB emBits in

  //em = [maskedDB; m1Hash; 0xbc]
  let em = create emLen (u8 0) in
  let em = update_sub em 0 dbLen maskedDB in
  let em = update_sub em dbLen hLen m1Hash in
  em.[emLen - 1] <- u8 0xbc

val pss_verify:
     #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> msg:lbytes msgLen
  -> emBits:size_pos
  -> em:lbytes (blocks emBits 8)
  -> bool
let pss_verify #msgLen sLen msg emBits em =
  let mHash = hash_sha256 msg in

  let emLen = blocks emBits 8 in
  let msBits = emBits % 8 in

  let em_0 = if msBits > 0 then em.[0] &. (u8 0xff <<. u32 msBits) else u8 0 in
  let em_last = em.[emLen - 1] in

  if (emLen < sLen + hLen + 2) then false
  else begin
    if (not (uint_to_nat #U8 em_last = 0xbc && uint_to_nat #U8 em_0 = 0)) then false
    else begin
      let dbLen = emLen - hLen - 1 in
      let maskedDB = sub em 0 dbLen in
      let m1Hash = sub em dbLen hLen in

      let dbMask = mgf_sha256 m1Hash dbLen in
      let db = xor_bytes maskedDB dbMask in
      let db = db_zero db emBits in

      let padLen = emLen - sLen - hLen - 1 in
      let pad2 = create padLen (u8 0) in
      let pad2 = pad2.[padLen - 1] <- u8 0x01 in

      let pad  = sub db 0 padLen in
      let salt = sub db padLen sLen in

      if not (eq_bytes pad pad2) then false
      else begin
        let m1Len = 8 + hLen + sLen in
        let m1 = create m1Len (u8 0) in
        let m1 = update_sub m1 8 hLen mHash in
        let m1 = update_sub m1 (8 + hLen) sLen salt in
        let m1Hash0 = hash_sha256 m1 in
        eq_bytes m1Hash0 m1Hash
      end
    end
  end

val rsapss_sign:
    #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> modBits:modBits{sLen + hLen + 2 <= blocks (modBits - 1) 8}
  -> eBits:size_pos
  -> dBits:size_pos
  -> pBits:size_pos
  -> qBits:size_pos
  -> skey:rsa_privkey modBits eBits dBits pBits qBits
  -> salt:lbytes sLen
  -> rBlind:bignum 64
  -> msg:lbytes msgLen
  -> lbytes (blocks modBits 8)
let rsapss_sign #sLen #msgLen modBits eBits dBits pBits qBits skey salt rBlind msg =
  let pkey = Mk_rsa_privkey?.pkey skey in
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let d = Mk_rsa_privkey?.d skey in
  let p = Mk_rsa_privkey?.p skey in
  let q = Mk_rsa_privkey?.q skey in

  let emBits = modBits - 1 in

  let em = pss_encode salt msg emBits in
  let m = bn_from_bytes_be em in
  //assume (bn_v m < bn_v n);
  admit();
  let s = rsa_blinding modBits n pBits p qBits q m dBits d rBlind in
  bn_to_bytes_be s

val rsapss_verify:
    #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> modBits:modBits
  -> eBits:size_pos
  -> pkey:rsa_pubkey modBits eBits
  -> sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> msg:lbytes msgLen
  -> sgnt:lbytes (blocks modBits 8)
  -> bool
let rsapss_verify #msgLen modBits eBits pkey sLen msg sgnt =
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in

  let emBits = modBits - 1 in

  let s = bn_from_bytes_be sgnt in
  admit();
  //assert (modBits <= 8 * blocks modBits 8);
  if bn_is_less s n then begin
    let m = mod_exp modBits n s eBits e in
    assume (bn_v m < pow2 emBits); // <- check this condition
    let m = bn_cast_le emBits m in
    let em = bn_to_bytes_be m in
    pss_verify sLen msg emBits em end
  else false
