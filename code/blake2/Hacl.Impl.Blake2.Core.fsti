module Hacl.Impl.Blake2.Core
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module Spec = Spec.Blake2_Vec

type m_spec =
  | M32
  | M128
  | M256

inline_for_extraction
unfold type word_t (a:Spec.alg) = Spec.word_t a

inline_for_extraction
unfold let element_t (a:Spec.alg) (m:m_spec) =
  match a,m with
  | Spec.Blake2S,M128 -> (vec_t U32 4)
  | Spec.Blake2S,M256 -> (vec_t U32 4)
  | Spec.Blake2B,M256 -> (vec_t U64 4)
  | _ -> (word_t a)

inline_for_extraction
val zero_element: a:Spec.alg -> m:m_spec -> element_t a m

inline_for_extraction
val row_len: a:Spec.alg -> m:m_spec -> size_t


inline_for_extraction
unfold let row_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (row_len a m)

inline_for_extraction
val row_v: #a:Spec.alg -> #m:m_spec -> h:mem -> row_p a m -> GTot (Spec.row a)

noextract
val row_v_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> r:row_p a m ->
  Lemma (ensures (as_seq h0 r == as_seq h1 r ==>
		  row_v h0 r == row_v h1 r))
	[SMTPat (row_v h0 r); SMTPat (row_v h1 r)]

inline_for_extraction
unfold let state_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (4ul *. row_len a m)

inline_for_extraction
unfold let index_t = n:size_t{v n < 4}

inline_for_extraction
let g_rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) : GTot (row_p a m) =
  gsub st (idx *. row_len a m) (row_len a m)

val g_rowi_disjoint: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx1:index_t -> idx2:index_t ->
  Lemma (ensures (idx1 <> idx2 ==> disjoint (g_rowi st idx1) (g_rowi st idx2)))
	[SMTPat (disjoint (g_rowi st idx1) (g_rowi st idx2))]

val g_rowi_unchanged: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (as_seq h0 st == as_seq h1 st))
	(ensures (as_seq h0 (g_rowi st i) == as_seq h1 (g_rowi st i)))
	[SMTPat (as_seq h0 (g_rowi st i)); SMTPat (as_seq h1 (g_rowi st i))]

val g_rowi_disjoint_other:  #a:Spec.alg -> #m:m_spec -> #b:Type -> #len:size_t -> st:state_p a m -> i:index_t -> x:lbuffer b len ->
  Lemma(requires (disjoint st x))
       (ensures (disjoint (g_rowi st i) x /\ disjoint x (g_rowi st i)))


inline_for_extraction noextract
val state_v: #a:Spec.alg -> #m:m_spec -> mem -> state_p a m -> GTot (Spec.state a)

noextract
val state_v_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st:state_p a m ->
  Lemma (requires (as_seq h0 st == as_seq h1 st))
	(ensures (state_v h0 st == state_v h1 st))
	[SMTPat (state_v h0 st); SMTPat (state_v h1 st)]


val modifies_row: a:Spec.alg -> m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (live h0 st /\ modifies (loc (g_rowi st i)) h0 h1))
	(ensures (state_v h1 st == Lib.Sequence.((state_v h0 st).[v i] <- row_v h1 (g_rowi st i))))
	[SMTPat (modifies (loc (g_rowi st i)) h0 h1)]


inline_for_extraction
val rowi: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx:index_t ->
	  ST (row_p a m)
	  (requires (fun h -> live h st))
	  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == g_rowi st idx))

inline_for_extraction
val xor_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 ^| row_v h0 r2 )))
inline_for_extraction
val add_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 +| row_v h0 r2 )))
inline_for_extraction
val ror_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:rotval (Spec.wt a) ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 >>>| r2 )))
inline_for_extraction
val permr_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> n:index_t ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( rotr (row_v h0 r1) (v n) )))

val create4_lemma: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a ->
  Lemma (ensures (Lib.Sequence.createL [x0;x1;x2;x3] == create4 x0 x1 x2 x3))
	[SMTPat (Lib.Sequence.createL [x0;x1;x2;x3])]

inline_for_extraction
val alloc_row: a:Spec.alg -> m:m_spec ->
	  StackInline (row_p a m)
	  (requires (fun h -> True))
	  (ensures (fun h0 r h1 -> stack_allocated r h0 h1 (Lib.Sequence.create (v (row_len a m)) (zero_element a m)) /\
				live h1 r /\
				row_v h1 r == Spec.zero_row a))

inline_for_extraction
val create_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> w0:word_t a -> w1:word_t a -> w2:word_t a -> w3:word_t a ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( create_row w0 w1 w2 w3 )))
inline_for_extraction
val load_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> ws:lbuffer (word_t a) 4ul ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h ws /\ disjoint r1 ws))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( load_row (as_seq h0 ws))))

inline_for_extraction
val gather_row: #a:Spec.alg -> #ms:m_spec -> #len:size_t -> r:row_p a ms -> m:lbuffer uint8 len ->
          i0: Spec.word_index a (v len) -> i1:Spec.word_index a (v len) -> i2:Spec.word_index a (v len) -> i3:Spec.word_index a (v len)
	  -> ST unit
	  (requires (fun h -> live h r /\ live h m /\ disjoint r m))
	  (ensures (fun h0 _ h1 -> modifies (loc r) h0 h1 /\
				row_v h1 r == Spec.( gather_row (as_seq h0 m) i0 i1 i2 i3)))


