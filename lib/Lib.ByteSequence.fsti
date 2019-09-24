module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

/// Definition of byte-based sequences

unfold inline_for_extraction
type bytes_l (l:secrecy_level) = seq (uint_t U8 l)

unfold inline_for_extraction
type lbytes_l (l:secrecy_level) (len:size_nat) = lseq (uint_t U8 l) len

unfold inline_for_extraction let bytes = bytes_l SEC
unfold inline_for_extraction let lbytes (len:size_nat) = lbytes_l SEC len
unfold inline_for_extraction let pub_bytes = bytes_l PUB
unfold inline_for_extraction let pub_lbytes (len:size_nat) = lbytes_l PUB len

(** Construct the equality mask for a pair of secret integer sequences *)
val seq_eq_mask: #t:inttype{~(S128? t)} -> #len1:size_nat -> #len2:size_nat
  -> b1:lseq (int_t t SEC) len1
  -> b2:lseq (int_t t SEC) len2
  -> len:size_nat{len <= len1 /\ len <= len2}
  -> res:int_t t SEC{
      (sub b1 0 len == sub b2 0 len  ==> v res == v (ones t SEC)) /\
      (sub b1 0 len =!= sub b2 0 len ==> v res == v (zeros t SEC))}

(** Compares two byte sequences and declassifies the result *)
inline_for_extraction
val lbytes_eq: #len:size_nat -> b1:lbytes len -> b2:lbytes len -> b:bool{b <==> b1 == b2}

/// Constant for empty lbytes

noextract
let lbytes_empty: lbytes 0 = create 0 (u8 0)

/// Conversions between natural numbers and sequences

inline_for_extraction
val nat_from_intseq_be: #t:inttype{unsigned t} -> #l:secrecy_level -> b:seq (uint_t t l)
  -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
val nat_from_intseq_le: #t:inttype{unsigned t} -> #l:secrecy_level
  -> b:seq (uint_t t l) -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
let nat_from_bytes_be (#l:secrecy_level) (b:bytes_l l) : n:nat{n < pow2 (length b * 8)} =
  nat_from_intseq_be #U8 #l b

inline_for_extraction
let nat_from_bytes_le (#l:secrecy_level) (b:bytes_l l) : n:nat{n < pow2 (length b * 8)} =
  nat_from_intseq_le #U8 #l b

inline_for_extraction
val nat_to_intseq_be: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> n:nat{n < pow2 (bits t * len)} ->
  b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_be b}

inline_for_extraction
val nat_to_intseq_le: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> n:nat{n < pow2 (bits t * len)} ->
  b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_le b}

inline_for_extraction
val nat_to_bytes_be: #l:secrecy_level -> len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes_l l{length b == len /\ n == nat_from_intseq_be #U8 b}

inline_for_extraction
val nat_to_bytes_le: #l:secrecy_level -> len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes_l l{length b == len /\ n == nat_from_intseq_le #U8 b}

inline_for_extraction
val uint_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> uint_t t l -> lbytes_l l (numbytes t)

val index_uint_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_le #t #l u) i ==
                              uint #U8 #l (v u / pow2 (op_Multiply 8 i) % pow2 8))

inline_for_extraction
val uint_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l -> lbytes_l l (numbytes t)

inline_for_extraction
val uint_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> b:lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uint_from_bytes_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uints_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

val index_uints_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> ul:lseq (uint_t t l) len -> i:nat{i < len * numbytes t}
  -> Lemma
    (index (uints_to_bytes_le #t #l #len ul) i == (uint_to_bytes_le ul.[i / numbytes t]).[i % numbytes t])

inline_for_extraction
val uints_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

inline_for_extraction
val uints_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len

val index_uints_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:size_nat{i < len}
  -> Lemma
    (index (uints_from_bytes_le #t #l #len b) i == uint_from_bytes_le (sub b (i * numbytes t) (numbytes t)))

inline_for_extraction
val uints_from_bytes_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len

val index_uints_from_bytes_be: #t:inttype{unsigned t /\ ~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:size_nat{i < len}
  -> Lemma
    (index (uints_from_bytes_be #t #l #len b) i == uint_from_bytes_be (sub b (i * numbytes t) (numbytes t)))

inline_for_extraction
val uint_at_index_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t)
  -> idx:nat{idx < len}
  -> u:uint_t t l{u == (uints_from_bytes_le #t #l #len b).[idx]}

inline_for_extraction
val uint_at_index_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t)
  -> idx:nat{idx < len}
  -> u:uint_t t l{u == (uints_from_bytes_be #t #l #len b).[idx]}

val nat_from_intseq_le_lemma0: #t:inttype{unsigned t} -> #l:secrecy_level -> b:lseq (uint_t t l) 1 ->
  Lemma (nat_from_intseq_le b == uint_v b.[0])

val nat_from_intseq_le_slice_lemma: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat
  -> b:lseq (uint_t t l) len -> i:nat{i <= len} ->
  Lemma (nat_from_intseq_le b == nat_from_intseq_le (Seq.slice b 0 i) + pow2 (i * bits t) * nat_from_intseq_le (Seq.slice b i len))

val uints_from_bytes_le_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_le (uints_from_bytes_le #t #l #len b) == nat_from_bytes_le b)

val uints_to_bytes_le_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> len:nat{len * numbytes t < pow2 32}
  -> n:nat{n < pow2 (bits t * len)} ->
  Lemma (uints_to_bytes_le #t #l #len (nat_to_intseq_le #t #l len n) == nat_to_bytes_le (len * numbytes t) n)

val nat_from_intseq_le_inj:
  #t:inttype{unsigned t} -> #l:secrecy_level -> b1:seq (uint_t t l) -> b2:seq (uint_t t l) ->
  Lemma
    (requires length b1 == length b2 /\ nat_from_intseq_le b1 == nat_from_intseq_le b2)
    (ensures Seq.equal b1 b2)
    (decreases (length b1))

val lemma_nat_to_from_bytes_be_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == length b} -> x:size_nat{x < pow2 (8 * len)} ->
  Lemma (nat_from_bytes_be (nat_to_bytes_be #l len x) == x)

val lemma_nat_to_from_bytes_le_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == length b} -> x:nat{x < pow2 (8 * len)} ->
  Lemma
  (requires (True))
  (ensures  (nat_from_bytes_le (nat_to_bytes_le #l len x) == x))

val lemma_uint_to_bytes_le_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> x:uint_t t l ->
  Lemma (nat_from_bytes_le (uint_to_bytes_le #t #l x) == uint_v x)

val lemma_nat_from_to_intseq_le_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> b:seq (uint_t t l){length b == len} ->
  Lemma (nat_to_intseq_le len (nat_from_intseq_le b) == b)

val lemma_nat_from_to_bytes_le_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == Lib.Sequence.length b} ->
  Lemma
  (requires (True))
  (ensures  (nat_to_bytes_le #l len (nat_from_bytes_le b)) == b)

val lemma_reveal_uint_to_bytes_le: #t:inttype{unsigned t /\ t <> U1} -> #l:secrecy_level -> b:bytes_l l{Lib.Sequence.length b == numbytes t} ->
  Lemma (nat_from_bytes_le b == uint_v (uint_from_bytes_le #t #l b))