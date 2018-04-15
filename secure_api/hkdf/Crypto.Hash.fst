(* Selected hash functions, with an agile interface and a
   multiplex-able implementation calling into Hacl.Hash. *)

module Crypto.Hash

open FStar.UInt32 
open FStar.HyperStack.ST

let string_of_alg = function
  | MD5    -> "MD5"
  | SHA1   -> "SHA1"
  | SHA224 -> "SHA224"
  | SHA256 -> "SHA256"
  | SHA384 -> "SHA384"
  | SHA512 -> "SHA512"

/// HACL*-based implementation, missing MD5 and SHA1 for now.
/// (commented out chunks provide earlier implementation details)

(*
let acc0 = function
  | MD5 ->  [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476] // A, B, C, D
  | SHA1 -> [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476; 0xc3d2e1f0] // h0--h4
  | SHA224 -> [0xc1059ed8; 0x367cd507; 0x3070dd17; 0xf70e5939; 0xffc00b31; 0x68581511; 0x64f98fa7; 0xbefa4fa4] // second 32 bits of the fractional parts of the square roots of the 9th through 16th primes 23..53
  | SHA256 -> [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19] // first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19
  | SHA384 -> [0xcbbb9d5dc1059ed8; 0x629a292a367cd507; 0x9159015a3070dd17; 0x152fecd8f70e5939; 0x67332667ffc00b31; 0x8eb44a8768581511; 0xdb0c2e0d64f98fa7; 0x47b5481dbefa4fa4]
  | SHA512 -> [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1; 0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]
*)


// 18-04-09 eta-expansions are *required* for Kremlin extraction. 
// 18-04-09 Even for no_extract functions! 

(* specification code *) 

let acc a = 
  match a with 
  | SHA256 -> Spec.SHA2_256.block_w
  | SHA384 -> Spec.SHA2_384.block_w
  | SHA512 -> Spec.SHA2_512.block_w

/// 18-04-10 verification is very slow, probably due to lots of HACL
/// context. And the specs are not matching anyway.

let acc0 #a = 
  match a with 
  | SHA256 -> Spec.SHA2_256.h_0
  | SHA384 -> Spec.SHA2_384.h_0
  | SHA512 -> Spec.SHA2_512.h_0

let compress #a st b =
  match a with 
  | SHA256 -> Spec.SHA2_256.shuffle st b
  | SHA384 -> Spec.SHA2_384.shuffle st b
  | SHA512 -> Spec.SHA2_512.shuffle st b

let finish #a st = 
  match a with 
  | SHA256 -> Spec.SHA2_256.finish st
  | SHA384 -> Spec.SHA2_384.finish st 
  | SHA512 -> Spec.SHA2_512.finish st 

let suffix a l = 
  let l1 = l % blockLength a in 
  let l0 = l - l1 in
  match a with
  | SHA256 -> Spec.SHA2_256.pad l0 l1
  | SHA384 -> Spec.SHA2_384.pad l0 l1
  | SHA512 -> Spec.SHA2_512.pad l0 l1

(* implementation *) 

let lemma_hash_spec a b = ()

let state_word a = 
  match a with 
  | SHA256 -> UInt32.t
  | SHA384 -> UInt64.t
  | SHA512 -> UInt64.t
let state_zero a = 
  match a with 
  | SHA256 -> 0ul
  | SHA384  
  | SHA512 -> 0UL
let state_size a =
  match a with 
  | SHA256 -> Hacl.Hash.SHA2_256.size_state
  | SHA384 -> Hacl.Hash.SHA2_384.size_state
  | SHA512 -> Hacl.Hash.SHA2_512.size_state

let as_acc #a h st = admit() //TODO as_seq (sub st ...)

let init_SHA256 acc = Buffer.upd acc (state_size SHA256 -^ 1ul) 0ul; Hacl.Hash.SHA2_256.init acc 
let init_SHA384 acc = Buffer.upd acc (state_size SHA256 -^ 1ul) 0UL; Hacl.Hash.SHA2_384.init acc 
let init_SHA512 acc = Buffer.upd acc (state_size SHA256 -^ 1ul) 0UL; Hacl.Hash.SHA2_512.init acc 

let init a acc = 
 match a with
  | SHA256 -> init_SHA256 acc
  | SHA384 -> init_SHA384 acc
  | SHA512 -> init_SHA512 acc

(*
let init a acc = 
 match a with
  | SHA256 -> Buffer.upd acc (state_size a -^ 1ul) 0ul; Hacl.Hash.SHA2_256.init acc 
  | SHA384 -> Buffer.upd acc (state_size a -^ 1ul) 0UL; Hacl.Hash.SHA2_384.init acc
  | SHA512 -> Buffer.upd acc (state_size a -^ 1ul) 0UL; Hacl.Hash.SHA2_512.init acc
*)

let update a st block = 
  match a with
  | SHA256 -> Hacl.Hash.SHA2_256.update st block
  | SHA384 -> Hacl.Hash.SHA2_384.update st block
  | SHA512 -> Hacl.Hash.SHA2_512.update st block

let update_multi a st blocks len = 
  match a with
  | SHA256 -> Hacl.Hash.SHA2_256.update_multi st blocks (len /^ blockLen SHA256)
  | SHA384 -> Hacl.Hash.SHA2_384.update_multi st blocks (len /^ blockLen SHA384)
  | SHA512 -> Hacl.Hash.SHA2_512.update_multi st blocks (len /^ blockLen SHA512)

let update_last a st last totlen =
  let len = totlen %^ blockLen a in 
  match a with 
  | SHA256 -> Hacl.Hash.SHA2_256.update_last st last len
  | SHA384 -> Hacl.Hash.SHA2_384.update_last st last (Int.Cast.uint32_to_uint64 len)
  | SHA512 -> Hacl.Hash.SHA2_512.update_last st last (Int.Cast.uint32_to_uint64 len)

let extract a st output = 
  match a with 
  | SHA256 -> Hacl.Hash.SHA2_256.finish st output
  | SHA384 -> Hacl.Hash.SHA2_384.finish st output
  | SHA512 -> Hacl.Hash.SHA2_512.finish st output

let compute a len input output = 
  match a with
  | SHA256 -> Hacl.Hash.SHA2_256.hash output input len
  | SHA384 -> Hacl.Hash.SHA2_384.hash output input len
  | SHA512 -> Hacl.Hash.SHA2_512.hash output input len

let agile_hash a output input len = compute a len input output 


