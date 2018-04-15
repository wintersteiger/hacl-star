(* Agile HMAC *)
module Crypto.HMAC
/// 18-03-03 Do we get specialized extraction of HMAC?

// for simplicity, we currently require that the key be block-sized;
// the standardized algorithm is more general.

open Crypto.Hash 

type bseq = Seq.seq UInt8.t 
let lbseq (l:nat) = b:bseq {Seq.length b = l}

let keysized (a:alg13) (l:nat) =
  l <= maxLength a /\ 
  l + blockLength a < pow2 32

(* ghost specification; the algorithmic definition is given in the .fst *)
noextract val hmac: 
  a: alg13 ->
  key: bseq{ keysized a (Seq.length key) } ->
  data: bseq{ Seq.length data + blockLength a <= maxLength a } ->
  lbseq (tagLength a)

open FStar.HyperStack.All
open FStar.Buffer

#reset-options "--max_fuel 0  --z3rlimit 20"
(* implementation, relying on 3 variants of SHA2 supported by HACL*; 
   we tolerate overlaps between tag and data. 
   (we used to require [disjoint data tag])
*)
val compute:
  a: alg13 ->
  tag: lbptr (tagLength a) ->
  key: bptr{ keysized a (length key) /\ disjoint key tag } -> 
  keylen: UInt32.t{ UInt32.v keylen = length key } ->
  data: bptr{ length data + blockLength a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = length data } -> 
  Stack unit
  (requires fun h0 -> live h0 tag /\ live h0 key /\ live h0 data)
  (ensures fun h0 _ h1 -> 
    live h1 tag /\ live h0 tag /\
    live h1 key /\ live h0 key /\
    live h1 data /\ live h0 data /\ 
    modifies_1 tag h0 h1 /\
    ( length data + blockLength a <= maxLength a /\ (* required for subtyping the RHS below *)    
      as_seq h1 tag == hmac a (as_seq h0 key) (as_seq h0 data)))
