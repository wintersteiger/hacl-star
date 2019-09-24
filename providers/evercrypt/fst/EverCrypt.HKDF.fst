module EverCrypt.HKDF

/// 18-03-04 to be compared to Hashing.HKDF, salvaged as a spec

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.Seq

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open FStar.Integers

open EverCrypt.Hash

open Spec.Hash.Definitions
open Spec.HKDF
friend Spec.HKDF

friend Lib.IntTypes

// [hashed] holds the HMAC text,
// of the form | Spec.Hash.Definitions.hash_len a | infolen | 1 |;
// its prefix is overwritten by HMAC at each iteration.

val hkdf_expand_loop:
  a       : EverCrypt.HMAC.supported_alg -> (
  okm     : B.buffer Lib.IntTypes.uint8 ->
  prk     : B.buffer Lib.IntTypes.uint8 ->
  prklen  : UInt32.t { UInt32.v prklen == B.length prk } ->
  infolen : UInt32.t ->
  len     : UInt32.t { UInt32.v len == B.length okm } ->
  hashed  : B.buffer Lib.IntTypes.uint8 { B.length hashed == Spec.Hash.Definitions.hash_length a + v infolen + 1} ->
  i       : UInt8.t {
    Spec.HMAC.keysized a (length prk) /\
    disjoint okm prk /\
    disjoint hashed okm /\
    disjoint hashed prk /\
    Spec.Hash.Definitions.hash_length a + v infolen + 1 + Spec.Hash.Definitions.block_length a < pow2 32 /\ (* specific to this implementation *)
    Spec.Hash.Definitions.hash_length a + pow2 32 + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a /\
    v i < 255 /\
    v len <= (255 - v i) * Spec.Hash.Definitions.hash_length a } ->
  Stack unit
  (requires fun h0 ->
    live h0 okm /\ live h0 prk /\ live h0 hashed)
  (ensures  fun h0 r h1 ->
    LowStar.Modifies.(modifies (loc_union (loc_buffer okm) (loc_buffer hashed)) h0 h1) /\ (
    let prk  = as_seq h0 prk in
    let info = as_seq h0 (gsub hashed (Hacl.Hash.Definitions.hash_len a) infolen) in
    let last = if i = 0uy then Seq.empty else as_seq h0 (gsub hashed 0ul (Hacl.Hash.Definitions.hash_len a)) in
    as_seq h1 okm == expand0 a prk info (v len) (v i) last)))

//18-07-13 how to improve this proof? should we use C.loops instead?
#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 800"
let rec hkdf_expand_loop a okm prk prklen infolen len hashed i =
  push_frame ();

  let tlen = Hacl.Hash.Definitions.hash_len a in
  let tag = sub hashed 0ul tlen in
  let info_counter = offset hashed tlen in
  let info = sub info_counter 0ul infolen in
  let counter = offset info_counter infolen in
  assert(disjoint tag info /\ disjoint tag counter /\ disjoint info counter);

  let h0 = ST.get() in  // initial state
  let i' = i + 1uy in
  counter.(0ul) <- i';

  let h1 = ST.get() in // before hashing
  Seq.lemma_eq_intro (as_seq h1 counter) (Seq.create 1 i');

  // derive an extra hash tag
  if i = 0uy then (
    // the first input is shorter, does not include the chaining block
    let len1 = infolen + 1ul in
    HMAC.compute a tag prk prklen info_counter len1;
    ( let h2 = ST.get() in
      let info = as_seq h0 info in
      let ctr1 = as_seq h1 counter in
      let prk  = as_seq h0 prk in
      let tag2 = as_seq h2 tag in
      let text = Seq.empty @| info @| ctr1  in
      // Seq.lemma_eq_intro (as_seq h1 counter) ctr1;
      // assert(tag2 == HMAC.hmac a v_prk (as_seq h1 hashed1));
      Seq.lemma_eq_intro (as_seq h1 info_counter) text;
      assert(tag2 == Spec.HMAC.hmac a prk text)  ))
  else (
    HMAC.compute a tag prk prklen hashed (tlen + infolen + 1ul);
    ( let h2 = ST.get() in
      let info = as_seq h0 info in
      let ctr1 = as_seq h1 counter in
      let prk  = as_seq h0 prk in
      let tag1 = as_seq h1 tag in
      let tag2 = as_seq h2 tag in
      let text = tag1 @| info @| ctr1 in
      // assert(tag2 == HMAC.hmac (Ghost.hide a) prk (as_seq h1 hashed));
      Seq.lemma_eq_intro (as_seq h1 hashed) text ;
      assert(tag2 == Spec.HMAC.hmac a prk text )));

  // copy it to the result; iterate if required
  let h2 = ST.get() in
  if len <= tlen then (
    blit tag 0ul okm 0ul len;
    ( let h3 = ST.get() in
      let prk  = as_seq h0 prk in
      let info = as_seq h0 info in
      let last = if i = 0uy then Seq.empty else as_seq h1 tag in
      let text = last @| info @| Seq.create 1 i' in
      let tag2 = as_seq h2 tag in
      let result = Seq.slice (as_seq h3 okm) 0 (v len) in
      // assert(tag2 == HMAC.hmac (Ghost.hide a) prk text);
      assert(result == Seq.slice tag2 0 (v len));
      assert(result == expand0 a prk info (v len) (v i) last) ))
  else (
    blit tag 0ul okm 0ul tlen;
    let h3 = ST.get() in
    let len' = len - tlen in
    let okm_tag = sub okm 0ul tlen in
    let okm' = offset okm tlen in
    hkdf_expand_loop a okm' prk prklen infolen len' hashed i';
    ( assert(disjoint okm_tag okm');
      let h4 = ST.get() in
      let info = as_seq h0 info in
      let prk  = as_seq h0 prk in
      let last = if i = 0uy then Seq.empty else as_seq h1 tag in
      let text = last @| info @| Seq.create 1 i' in
      let tag2 = as_seq h2 tag in
      // assert(tag2 == HMAC.hmac (Ghost.hide a) prk text);
      assert(tag2 == as_seq h4 okm_tag);
      let okm' = as_seq h4 okm' in
      Seq.lemma_eq_intro (tag2 @| okm') (as_seq h4 okm);
      assert(        okm' == expand0 a prk info (v len') (v i') tag2);
      assert(tag2 @| okm' == expand0 a prk info (v len) (v i) last)
    ));
  pop_frame()


let hkdf_extract a prk salt saltlen ikm ikmlen =
    HMAC.compute a prk salt saltlen ikm ikmlen

let hkdf_expand a okm prk prklen info infolen len =
  push_frame();
  let tlen = Hacl.Hash.Definitions.hash_len a in
  let text = LowStar.Buffer.alloca 0uy (tlen + infolen + 1ul) in
  blit info 0ul text tlen infolen;
  assert (Spec.Hash.Definitions.hash_length a <= 64);
  assert (Spec.Hash.Definitions.block_length a <= 128);
  assert_norm (64 + pow2 32 + 128 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(
    Spec.Hash.Definitions.hash_length a + pow2 32 + Spec.Hash.Definitions.block_length a < Spec.Hash.Definitions.max_input_length a);
  hkdf_expand_loop a okm prk prklen infolen len text 0uy;
  pop_frame()