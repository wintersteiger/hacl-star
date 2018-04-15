(* Selected hash functions, with an agile interface and a
   multiplex-able implementation calling into Hacl.Hash. *)

module Crypto.Hash

include EverCrypt.Hash

/// adapted from [tls/src/Hashing.*]

open FStar.UInt32 
open FStar.HyperStack.ST

#reset-options "--initial_ifuel 2 --initial_fuel 2 --z3rlimit 50"

type bseq = Seq.seq UInt8.t 
let lbseq (l:nat) = b:bseq {Seq.length b = l}

(* SUPPORTED ALGORITHMS; the first 3 are still required by TLS 1.2,
   included for legacy purpose only, and not provided by HACL*.  See
   e.g. https://en.wikipedia.org/wiki/SHA-1 for a global comparison
   and lengths *)
type alg =
  | MD5
  | SHA1
  | SHA224 
  | SHA256
  | SHA384
  | SHA512
//| SHAKE128 of (n:nat{n >= 8})
//| SHAKE256 of (n:nat{n >= 16})

val string_of_alg: alg -> string 

(* the algorithms used in TLS 1.3; we will make security assumptions
   only for constructions based on those. *)
type alg13 = a:alg {a=SHA256 \/ a=SHA384 \/ a=SHA512}

(* INPUT BLOCK SIZE, in bytes; useful to compute various lengths. *) 
let blockLen = function
  | MD5 | SHA1 | SHA224 | SHA256 ->  64ul
  | SHA384 | SHA512              -> 128ul
//| SHAKE128 _ -> 168 | SHAKE256 _ -> 136
  
noextract 
let blockLength a = UInt32.v (blockLen a)

(* RESULT TAGS and their lengths, in bytes *)

let maxTagLen = 64ul
let tagLen (a:alg) : Tot UInt32.t =
  match a with
  | MD5    -> 16ul
  | SHA1   -> 20ul
  | SHA224 -> 28ul // truncated SHA256
  | SHA256 -> 32ul
  | SHA384 -> 48ul // truncated SHA512
  | SHA512 -> 64ul
noextract let tagLength a = v (tagLen a)
let lemma_maxLen (a:alg) = assert_norm(tagLen a <=^ maxTagLen)

// used in TLS?
let lbytes l = b:Bytes.bytes {Bytes.length b = l}
type tag (a:alg) = b: lbytes (tagLength a)
type anyTag = lbytes (v maxTagLen)

// to be imported from HACL* 
noextract let maxLength: alg -> nat = fun a -> pow2 61 - 1 

noextract let lemma_maxLength (a:alg13) = assert_norm (pow2 32 <= maxLength a) 
noextract let hashable (a:alg) = b: bseq{ Seq.length b <= maxLength a }

(* MERKLE-DAMGARD algorithmic specification; not yet an incremental
   algorithms for all byte lengths; used for aligning specs and
   implementations but irrelevant for using hashes.  *)

noextract val acc (a:alg): Type0 // noeq, but `noeq val` is not supported)

(* sets the initial value of the accumulator *) 
noextract val acc0: #a:alg -> acc a 

(* hashes one block of data into the accumulator *)
noextract val compress: #a:alg -> acc a -> b: lbseq (blockLength a) -> acc a 

(* extracts the tag from the (possibly larger) accumulator *)
noextract val finish: #a:alg -> acc a -> lbseq (tagLength a)
 
// val hash2: #a:alg -> acc a -> b:bytes {length b % blockLength a = 0} -> acc a (decreases (length b))
noextract let rec hash2 
  (#a:alg) 
  (v:acc a) 
  (b:bseq {Seq.length b % blockLength a = 0}): 
  Tot (acc a) (decreases (Seq.length b))
=  
  if Seq.length b = 0 then v
  else
    let c,b = Seq.split b (blockLength a) in
    hash2 (compress v c) b

let lemma_compress 
  (#a: alg) 
  (a0: acc a)
  (c: lbseq (blockLength a)): 
  Lemma (compress a0 c == hash2 a0 c) = ()

let rec lemma_hash2 
  (#a: alg) 
  (a0: acc a)
  (b0 b1: (b:bseq{ Seq.length b % blockLength a = 0})): 
  Lemma 
    (ensures hash2 a0 (Seq.append b0 b1) == hash2 (hash2 a0 b0) b1)
    (decreases (Seq.length b0)) 
=
  if Seq.length b0 = 0 then (
    Seq.lemma_empty b0;
    Seq.append_empty_l b1 )
  else (
    let c,b0' = Seq.split b0 (blockLength a) in
    let c',b' = Seq.split (Seq.append b0 b1) (blockLength a) in
    Seq.append_assoc c b0' b1;
    //Seq.lemma_split b0 (blockLength a);
    //Seq.lemma_eq_intro (Seq.append b0 b1) (Seq.append c' b');
    Seq.lemma_eq_intro c c';
    Seq.lemma_eq_intro b' (Seq.append b0' b1);
    lemma_hash2 (hash2 a0 c) b0' b1)

noextract let hash0 (#a:alg) (b:bseq {Seq.length b % blockLength a = 0}) = hash2 (acc0 #a) b

(* PADDING AND LENGTH ENCODING *) 

// for convenience, we treat inputs as sequences of bytes, not bits.
// but note what's encoded in the suffix is the length in bits.
private noextract
let suffixLength (a:alg13) (length:nat {length <= maxLength a}): 
  n:nat{ (length + n) % blockLength a = 0 /\ n <= blockLength a + 9 } 
=
  let blocklen = v (blockLen a) in 
  let lenlen = match a with | SHA384 | SHA512 -> 8 | _ -> 4 in
  let required =  length + 1 + lenlen in // minimal length after padding and encoding the length
  let zeros = // minimal extra padding for block alignment
    if required % blocklen = 0 
    then 0
    else blocklen - (required % blocklen) in
    //was, harder to prove: required + blockLen a - ((required - 1) % blockLen a + 1) in
  1 + zeros + lenlen

noextract val suffix: a:alg13 -> l:nat {l <= maxLength a} -> lbseq (suffixLength a l)

noextract let spec (a:alg13) (b:hashable a): lbseq (tagLength a) =
  let blocks = Seq.append b (suffix a (Seq.length b)) in
  let acc = hash0 blocks in
  let tag = finish acc in
  tag

// TODO most users of the spec would prefer an opaque specification.
// noextract abstract let hash (a:alg13) (b: hashable a): lbseq (tagLength a) = spec a b 


(* ABSTRACT, EXTERNAL SPECIFICATION *) 

/// 18-04-07 postponing verified integration with HACL* for now. We
/// provide below a concise definition of the Merkle-Damgard
/// construction. The plan is to integrate it with Benjamin's
/// algorithmic specifications. At that point, we will probably hide
/// the construction behind the provider interface (since we don't
/// care about the construction when using or reasoning about them).

// 18-04-07 
(* 
let lemma_blockLengths = 
  assert_norm(
    blockLength SHA256 == Spec.SHA2_256.size_block /\
    blockLength SHA384 == Spec.SHA2_384.size_block /\
    blockLength SHA512 == Spec.SHA2_512.size_block)

noextract let lemma_tagLengths = 
  assert_norm(
    tagLength SHA256 == Spec.SHA2_256.size_hash /\
    // truncated SHA512; note that `size_hash` is 64, not 48
    tagLength SHA384 == Spec.SHA2_384.(size_word `op_Multiply` size_hash_final_w) /\
    tagLength SHA512 == Spec.SHA2_512.size_hash)

//#reset-options "--initial_ifuel 2 --initial_fuel 2 --z3rlimit 30"
(* maximal input size, in bytes *)
noextract let maxLength: alg -> nat = function
  // 18-03-02 hacl-star uses a strict inequality; why?
  | SHA256 -> Spec.SHA2_256.max_input_len_8 - 1 
  | SHA384 -> Spec.SHA2_384.max_input_len_8 - 1 
  | SHA512 -> Spec.SHA2_512.max_input_len_8 - 1
  | _      -> pow2 61 (* conservative *)

noextract 
let hash (a:alg13) (b: hashable a): lbseq (tagLength a) = 
  match a with 
  | SHA256 -> Spec.SHA2_256.hash b
  | SHA384 -> Spec.SHA2_384.hash b
  | SHA512 -> Spec.SHA2_512.hash b

val lemma_hash_spec: a:alg13 -> b: hashable a -> Lemma (hash a b = spec a b)
*)



/// Next, we provide abstract interface to the stateful implementation, in 3 styles:
///
/// - a lower-level interface reflects the building blocks; they are
///   used to build HMAC; they suffice to build the two other interfaces
/// 
/// - a simpler, one-shot interface for computing a hash
/// 
/// - a more flexible, incremental interface (WIP)

type bptr = Buffer.buffer UInt8.t 
let lbptr (l:nat)= b:bptr {Buffer.length b = l}
let bptrlen (b:bptr) = len:UInt32.t {UInt32.v len = Buffer.length b}

(* LOWER-LEVEL INTERFACE supporting agile incremental hash, hmac, etc *)

// based on Crypto.HMAC, removing the agile_ prefixes

(* convenient but a bit too concrete; the caller will allocate. See also the hack in Crypto.HMAC, and the need for disjointness. *)

(* not any more: 
// FIXME(adl): hash state allocation
// The type of state a is a buffer of uint32 for SHA256
// but a buffer of uint64 for SHA384 and SHA512
// This is hard to do in KreMLin (see Crypto.Symmetric.PRF)
// For now, we fake a u64[n] by allocation a u32[2*n]
// and rely on the implicit cast in C
*)


// experimenting with buffer abstraction--not so light.
val state_word: alg13 -> Type0
val state_zero: a: alg13 -> state_word a
val state_size: alg13 -> UInt32.t 

noextract 
let state (a:alg13) = 
  b: Buffer.buffer (state_word a) {Buffer.length b = v (state_size a)}

(* the more concrete pattern-matching below require more type annotations
  match a with
  | SHA256 -> b:Buffer.buffer UInt32.t {Buffer.length b = v (state_size SHA256)}
  | SHA384 -> b:Buffer.buffer UInt64.t {Buffer.length b = v (state_size SHA384)}
  | SHA512 -> b:Buffer.buffer UInt64.t {Buffer.length b = v (state_size SHA512)}
*)
noextract val as_acc: #a:alg13 -> h:HyperStack.mem -> state a -> acc a

let init_t  
  (a:alg13) =  
  st:state a -> Stack unit 
  (requires fun h0 -> Buffer.live h0 st)
  (ensures fun h0 () h1 -> 
    Buffer.live  h1 st /\
    Buffer.modifies_1 st h0 h1  /\ 
    as_acc h1 st == acc0 #a)

val init: a:alg13 -> init_t a

// Our SHA2 interface is parametric in its supported tag lengths:
// 224,256, 384, or 512 bits. (This is convenient but arbitrary.)
//
// A flat interface would provide instead:
// val init_SHA256: init_t SHA256
// val init_SHA384: init_t SHA384
// val init_SHA512: init_t SHA512

val update:
  a:alg13 -> 
  st:state a -> 
  block: lbptr (blockLength a) {Buffer.disjoint st block} -> 
  Stack unit 
  (requires fun h0 -> 
    Buffer.live h0 st /\ 
    Buffer.live h0 block)
  (ensures fun h0 () h1 -> 
    Buffer.live h1 st /\ 
    Buffer.live h1 block /\
    Buffer.modifies_1 st h0 h1 /\ 
    as_acc h1 st == compress (as_acc h0 st) (Buffer.as_seq h0 block))


// 18-03-03 update_multi is a parametric loop best left to the
// caller---unless we expect it to be further optimized.
// *note change of calling convention on the length*
val update_multi:
  a:alg13 -> 
  st:state a -> 
  blocks: bptr {Buffer.length blocks % blockLength a = 0 /\ Buffer.disjoint st blocks} -> 
  len: UInt32.t {v len = Buffer.length blocks} -> 
  Stack unit 
  (requires fun h0 -> 
    Buffer.live h0 st /\ 
    Buffer.live h0 blocks)
  (ensures fun h0 () h1 -> 
    Buffer.live h1 st /\ 
    Buffer.live h1 blocks /\
    Buffer.modifies_1 st h0 h1 /\ 
    as_acc h1 st == hash2 (as_acc h0 st) (Buffer.as_seq h0 blocks))

// 18-03-05 note the *new length-passsing convention*
// 18-03-03 it would be simpler to let the caller keep track of lengths!
// 18-03-03 the last block is *never* complete, so there is room for the 1st byte of padding.
#set-options "--z3rlimit 100"
val update_last:
  a:alg13 -> 
  st:state a -> 
  last: bptr {Buffer.length last <= blockLength a /\ Buffer.disjoint st last} -> 
  total_len: UInt32.t {
    let l = v total_len in 
    l <= maxLength a /\ 
    Buffer.length last = l % blockLength a } ->
  Stack unit 
  (requires fun h0 -> 
    Buffer.live #(state_word a) h0 st /\ Buffer.live h0 last)
  (ensures fun h0 () h1 -> 
    Buffer.live #(state_word a) h1 st /\ Buffer.live h1 last /\
    Buffer.modifies_1 #(state_word a) st h0 h1 /\ (
    let last0 = Buffer.as_seq h0 last in 
    as_acc h1 st == hash2 (as_acc h0 st) (Seq.append last0 (suffix a (v total_len)))))
// 18-04-13 typing above is brittle, not sure why


// for HandshakeLog we will need a variant that copies the state,
// finalizes, and extracts to compute successive hashes of the
// transcript.

// 18-03-03 can't also be named finished
val extract: 
  a:alg13 -> 
  st:state a -> 
  output: lbptr (tagLength a) {Buffer.disjoint st output} -> 
  Stack unit 
  (requires fun h0 -> 
    Buffer.live h0 st /\ Buffer.live h0 output)
  (ensures fun h0 () h1 -> 
    Buffer.live h1 st /\ Buffer.live h1 output /\
    Buffer.modifies_1 output h0 h1 /\ 
    Buffer.as_seq h1 output = finish (as_acc h0 st))


(* ONE-SHOT IMPLEMENTATION; implementatable from the lower-level
interface above. No need for an explicit bound since len <= 2^32 *)

(* alternative seq, vec, ptr
type uint8_s = Seq.seq UInt8.t
type uint8_v = 
type uint8_p = Buffer.buffer UInt8.t 
*)

val compute: 
  a: alg13 -> 
  len: UInt32.t -> 
  input: lbptr (v len) -> 
  output: lbptr (tagLength a){ Buffer.disjoint input output } -> Stack unit
  (requires fun h0 -> 
    Buffer.live h0 input /\ Buffer.live h0 output)
  (ensures fun h0 () h1 -> 
    Buffer.live h1 input /\ Buffer.live h1 output /\
    Buffer.modifies_1 output h0 h1 /\
    v len <= maxLength a /\ (* required for subtyping the RHS below *)
    Buffer.as_seq h1 output = spec a (Buffer.as_seq h0 input))

// same as compute with permuted arguments; included for backward
// compatibility with secure_api
val agile_hash: 
  a: alg13 -> 
  output: lbptr (tagLength a) -> 
  input: bptr -> 
  len: UInt32.t -> 
  Stack unit
  (requires fun h0 -> 
    Buffer.disjoint input output /\ 
    Buffer.length input = v len /\
    Buffer.live h0 input /\ Buffer.live h0 output)
  (ensures fun h0 () h1 -> 
    Buffer.live h1 input /\ Buffer.live h1 output /\
    Buffer.modifies_1 output h0 h1 /\
    v len <= maxLength a /\ (* required for subtyping the RHS below *)
    Buffer.as_seq h1 output = spec a (Buffer.as_seq h0 input))
 
(* TODO a third, incremental-hash implementation. *)

/// INCREMENTAL HASHING (working notes)
/// The state includes
/// - the accumulator (one or two blocks?)
/// - the total length of inputs (len)
/// - a partial block containing the rest of the prior input,
///   of length len % blockSize a.
///
/// To accumulate any number of bytes:
/// - we first (conditionally) copy the start of the input to complete
///   the partial block, and update
/// - we loop over complete blocks from the input
/// - we finally copy the rest to the partial block.
///
/// We could also use the partial block for padding and finishing
/// (with one or two extra compressions). In this style, update_last
/// would get a full, partially-filled block from the caller, rather
/// than allocate its own, to be completed & compressed with 10*llll,
/// in one or two steps.
/// - add 1
/// - if it won't fit, pad with 0s & compress, and reset position to 0.
/// - pad with 0s, encode length at the end of the block & compress.
///
/// To fork hash chains is straightforward: just copy the state on top
/// of the stack before finishing.
///
/// Can we get the compression function and the loop coded in VALE?



/// We finally provide high-level-bytes implementation wrappers.
/// (currently used for idealization in secure_api and TLS
/// 
(* functional implementation wrapper *)

// TODO missing BufferBytes here
// val eval: a: alg13 -> b: Bytes.bytes -> Stack (Bytes.lbytes (tagLength a))
//   (requires fun h -> True)
//   (ensures fun h0 tag h1 -> Bytes.reveal tag = hash a (Bytes.reveal b) /\ h0 == h1)


