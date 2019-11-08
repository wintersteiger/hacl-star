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
unfold let zero_element (a:Spec.alg) (m:m_spec) : element_t a m =
  match a,m with
  | Spec.Blake2S,M128 -> (vec_zero U32 4)
  | Spec.Blake2S,M256 -> (vec_zero U32 4)
  | Spec.Blake2B,M256 -> (vec_zero U64 4)
  | _ -> Spec.zero a

inline_for_extraction
unfold let row_len (a:Spec.alg) (m:m_spec) : size_t =
  match a,m with
  | Spec.Blake2S,M128 -> 1ul
  | Spec.Blake2S,M256 -> 1ul
  | Spec.Blake2B,M256 -> 1ul
  | _ -> 4ul

inline_for_extraction
unfold let row_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (row_len a m)

inline_for_extraction
val row_v: #a:Spec.alg -> #m:m_spec -> h:mem -> row_p a m -> GTot (Spec.row a)
inline_for_extraction
let row_v #a #m h r =
  match a,m with
  | Spec.Blake2S,M128 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | Spec.Blake2S,M256 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | Spec.Blake2B,M256 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | _ -> as_seq h r

noextract
val row_v_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> r:row_p a m ->
  Lemma (ensures (as_seq h0 r == as_seq h1 r ==>
		  row_v h0 r == row_v h1 r))
	[SMTPat (row_v h0 r); SMTPat (row_v h1 r)]
let row_v_lemma #a #m h0 h1 r = ()

inline_for_extraction
unfold let state_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (4ul *. row_len a m)

inline_for_extraction
unfold let index_t = n:size_t{v n < 4}

inline_for_extraction
let g_rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) : GTot (row_p a m) =
  gsub st (idx *. row_len a m) (row_len a m)

#push-options "--z3rlimit  50"
val g_rowi_disjoint: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx1:index_t -> idx2:index_t ->
  Lemma (ensures (idx1 <> idx2 ==> disjoint (g_rowi st idx1) (g_rowi st idx2)))
	[SMTPat (disjoint (g_rowi st idx1) (g_rowi st idx2))]
let g_rowi_disjoint #a #m st idx1 idx2 =
  if idx1 <. idx2 then (
    assert (v (idx1 *. row_len a m) + v (row_len a m) <= v (idx2 *. row_len a m));
    assert (g_rowi st idx1 ==
	    gsub st (idx1 *. row_len a m) (row_len a m));
    assert (g_rowi st idx2 ==
	    gsub st (idx2 *. row_len a m) (row_len a m));
   LowStar.Monotonic.Buffer.loc_disjoint_gsub_buffer #_ #((LowStar.Buffer.trivial_preorder (element_t a m))) #((LowStar.Buffer.trivial_preorder (element_t a m))) st (idx1 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)) (idx2 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m))
    )
  else if idx2 <. idx1 then (
    assert (v (idx2 *. row_len a m) + v (row_len a m) <= v (idx1 *. row_len a m));
    assert (g_rowi st idx2 ==
	    gsub st (idx2 *. row_len a m) (row_len a m));
    LowStar.Monotonic.Buffer.loc_disjoint_gsub_buffer #_ #((LowStar.Buffer.trivial_preorder (element_t a m))) #((LowStar.Buffer.trivial_preorder (element_t a m))) st (idx1 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)) (idx2 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)))
  else ()

val g_rowi_unchanged: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (as_seq h0 st == as_seq h1 st))
	(ensures (as_seq h0 (g_rowi st i) == as_seq h1 (g_rowi st i)))
	[SMTPat (as_seq h0 (g_rowi st i)); SMTPat (as_seq h1 (g_rowi st i))]
let g_rowi_unchanged #a #m h0 h1 st i =
  assert (v (i *. row_len a m) + v (row_len a m) <= length st);
  LowStar.Monotonic.Buffer.as_seq_gsub #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) h0 st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m));
  LowStar.Monotonic.Buffer.as_seq_gsub #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) h1 st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m))

val g_rowi_disjoint_other:  #a:Spec.alg -> #m:m_spec -> #b:Type -> #len:size_t -> st:state_p a m -> i:index_t -> x:lbuffer b len ->
  Lemma(requires (disjoint st x))
       (ensures (disjoint (g_rowi st i) x /\ disjoint x (g_rowi st i)))
let g_rowi_disjoint_other #a #m #b #len st i x =
  assert (v (i *. row_len a m) + v (row_len a m) <= length st);
    LowStar.Monotonic.Buffer.loc_includes_gsub_buffer_r'  #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m))
#pop-options

inline_for_extraction
let state_v (#a:Spec.alg) (#m:m_spec) (h:mem) (st:state_p a m) : GTot (Spec.state a) =
  let r0 = row_v h (g_rowi st 0ul) in
  let r1 = row_v h (g_rowi st 1ul) in
  let r2 = row_v h (g_rowi st 2ul) in
  let r3 = row_v h (g_rowi st 3ul) in
  create4 r0 r1 r2 r3

noextract
val state_v_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st:state_p a m ->
  Lemma (requires (as_seq h0 st == as_seq h1 st))
	(ensures (state_v h0 st == state_v h1 st))
	[SMTPat (state_v h0 st); SMTPat (state_v h1 st)]
let state_v_lemma #a #m h0 h1 st = ()


#push-options "--z3rlimit 50"
val modifies_row: a:Spec.alg -> m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (live h0 st /\ modifies (loc (g_rowi st i)) h0 h1))
	(ensures (state_v h1 st == Lib.Sequence.((state_v h0 st).[v i] <- row_v h1 (g_rowi st i))))
	[SMTPat (modifies (loc (g_rowi st i)) h0 h1)]
let modifies_row a m h0 h1 st i =
    assert (live h0 (g_rowi st 0ul));
    assert (live h0 (g_rowi st 1ul));
    assert (live h0 (g_rowi st 2ul));
    assert (live h0 (g_rowi st 3ul));
    Lib.Sequence.(eq_intro (state_v h1 st) ((state_v h0 st).[v i] <- row_v h1 (g_rowi st i)))
#pop-options


inline_for_extraction
val rowi: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx:index_t ->
	  ST (row_p a m)
	  (requires (fun h -> live h st))
	  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == g_rowi st idx))

inline_for_extraction
let rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) =
  sub st (idx *. row_len a m) (row_len a m)


inline_for_extraction
val xor_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 ^| row_v h0 r2 )))
inline_for_extraction
let xor_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_xor #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (logxor #(Spec.wt a) #SEC) r1 r2


inline_for_extraction
val add_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 +| row_v h0 r2 )))
inline_for_extraction
let add_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_add_mod #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (add_mod #(Spec.wt a) #SEC) r1 r2


inline_for_extraction
val ror_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:rotval (Spec.wt a) ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 >>>| r2 )))
inline_for_extraction
let ror_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_rotate_right #U32 #4 r1.(0ul) r2
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_rotate_right #U32 #4 r1.(0ul) r2
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_rotate_right #U64 #4 r1.(0ul) r2
  | _ ->
    let r1:lbuffer (Spec.word_t a) 4ul = r1 in
    mapT 4ul r1 (rotate_right_i #(Spec.wt a) #SEC r2) r1


inline_for_extraction
val permr_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> n:index_t ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( rotr (row_v h0 r1) (v n) )))

#push-options "--z3rlimit 50"
inline_for_extraction
let permr_row #a #m r1 n =
  let n0,n1,n2,n3 = n,(n+.1ul)%.4ul,(n+.2ul)%.4ul,(n+.3ul)%.4ul in
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128 ->
    let v0 : vec_t U32 4 = r1.(0ul) in
    let v1 : vec_t U32 4 = vec_permute4 #U32 v0 n0 n1 n2 n3 in
    Lib.Sequence.(eq_intro (create4 (vec_v v0).[v n0] (vec_v v0).[v n1] (vec_v v0).[v n2] (vec_v v0).[v n3]) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (Spec.rotr (vec_v v0) (v n)) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    r1.(0ul) <- v1
  | Spec.Blake2B,M256 ->
    let v0 : vec_t U64 4 = r1.(0ul) in
    let v1 : vec_t U64 4 = vec_permute4 #U64 v0 n0 n1 n2 n3 in
    Lib.Sequence.(eq_intro (create4 (vec_v v0).[v n0] (vec_v v0).[v n1] (vec_v v0).[v n2] (vec_v v0).[v n3]) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (Spec.rotr (vec_v v0) (v n)) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    r1.(0ul) <- v1
  | _ ->
    let h0 = ST.get() in
    let r1:lbuffer (Spec.word_t a) 4ul = r1 in
    let x0 = r1.(n0) in
    let x1 = r1.(n1) in
    let x2 = r1.(n2) in
    let x3 = r1.(n3) in
    r1.(0ul) <- x0;
    r1.(1ul) <- x1;
    r1.(2ul) <- x2;
    r1.(3ul) <- x3;
    let h1 = ST.get() in
    Lib.Sequence.(let s0 = as_seq h0 r1 in eq_intro (create4 x0 x1 x2 x3) (createi 4 (fun i -> s0.[(i+v n)%4])));
    Lib.Sequence.(let s0 = as_seq h0 r1 in eq_intro (Spec.rotr s0 (v n)) (Lib.Sequence.(createi 4 (fun i -> s0.[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (as_seq h1 r1) (create4 x0 x1 x2 x3));
    ()
#pop-options

#push-options "--z3rlimit 50"
val create4_lemma: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a ->
  Lemma (ensures (Lib.Sequence.createL [x0;x1;x2;x3] == create4 x0 x1 x2 x3))
	[SMTPat (Lib.Sequence.createL [x0;x1;x2;x3])]
let create4_lemma #a x0 x1 x2 x3 =
  let open Lib.Sequence in
  let l : list a = [x0;x1;x2;x3] in
  assert_norm (List.Tot.index l 0 == x0);
  assert_norm (List.Tot.index l 1 == x1);
  assert_norm (List.Tot.index l 2 == x2);
  assert_norm (List.Tot.index l 3 == x3);
  let s1 : lseq a 4 = of_list l in
  let s2 : lseq a 4 = create4 x0 x1 x2 x3 in
  eq_intro s1 s2
#pop-options

inline_for_extraction
val alloc_row: a:Spec.alg -> m:m_spec ->
	  StackInline (row_p a m)
	  (requires (fun h -> True))
	  (ensures (fun h0 r h1 -> stack_allocated r h0 h1 (Lib.Sequence.create (v (row_len a m)) (zero_element a m)) /\
				live h1 r /\
				row_v h1 r == Spec.zero_row a))

inline_for_extraction
let alloc_row a m = create (row_len a m) (zero_element a m)


inline_for_extraction
val create_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> w0:word_t a -> w1:word_t a -> w2:word_t a -> w3:word_t a ->
	  ST unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( create_row w0 w1 w2 w3 )))

inline_for_extraction
let create_row #a #m r w0 w1 w2 w3 =
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128
  | Spec.Blake2B,M256 ->
    r.(0ul) <- vec_load4 w0 w1 w2 w3
  | _ ->
    r.(0ul) <- w0;
    r.(1ul) <- w1;
    r.(2ul) <- w2;
    r.(3ul) <- w3;
    let h1 = ST.get() in
    Lib.Sequence.eq_intro (as_seq h1 r) (create4 w0 w1 w2 w3)

inline_for_extraction
val load_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> ws:lbuffer (word_t a) 4ul ->
	  ST unit
	  (requires (fun h -> live h r1 /\ live h ws /\ disjoint r1 ws))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( load_row (as_seq h0 ws))))

inline_for_extraction
let load_row #a #m r ws = create_row r ws.(0ul) ws.(1ul) ws.(2ul) ws.(3ul)

inline_for_extraction
val gather_row: #a:Spec.alg -> #ms:m_spec -> #len:size_t -> r:row_p a ms -> m:lbuffer uint8 len ->
          i0: Spec.word_index a (v len) -> i1:Spec.word_index a (v len) -> i2:Spec.word_index a (v len) -> i3:Spec.word_index a (v len)
	  -> ST unit
	  (requires (fun h -> live h r /\ live h m /\ disjoint r m))
	  (ensures (fun h0 _ h1 -> modifies (loc r) h0 h1 /\
				row_v h1 r == Spec.( gather_row (as_seq h0 m) i0 i1 i2 i3)))

#push-options "--z3rlimit 100"
inline_for_extraction
let gather_row #a #ms #len r m i0 i1 i2 i3 =
  let h0 = ST.get() in
  let nb = size (Spec.size_word a) in
  let b0 = sub m (i0 *. nb) nb in
  let b1 = sub m (i1 *. nb) nb in
  let b2 = sub m (i2 *. nb) nb in
  let b3 = sub m (i3 *. nb) nb in
  as_seq_gsub h0 m (i0 *. nb) nb;
  as_seq_gsub h0 m (i1 *. nb) nb;
  as_seq_gsub h0 m (i2 *. nb) nb;
  as_seq_gsub h0 m (i3 *. nb) nb;
  assert (as_seq h0 b0 == Lib.Sequence.sub (as_seq h0 m) (v i0 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b1 == Lib.Sequence.sub (as_seq h0 m) (v i1 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b2 == Lib.Sequence.sub (as_seq h0 m) (v i2 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b3 == Lib.Sequence.sub (as_seq h0 m) (v i3 * Spec.size_word a) (Spec.size_word a));
  let u0 = uint_from_bytes_le #(Spec.wt a) b0 in
  let u1 = uint_from_bytes_le #(Spec.wt a) b1 in
  let u2 = uint_from_bytes_le #(Spec.wt a) b2 in
  let u3 = uint_from_bytes_le #(Spec.wt a) b3 in
  assert (u0 == Lib.ByteSequence.uint_from_bytes_le (as_seq h0 b0));
  create_row r u0 u1 u2 u3
#pop-options

  
