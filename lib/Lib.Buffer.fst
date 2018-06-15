module Lib.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies

module I = Lib.IntTypes

module LSeq = Lib.Sequence
module U32 = FStar.UInt32

let lbuffer a len = (b: B.buffer a { B.length b == len } )

let gsub #a #len #olen b start n =
  B.gsub b (U32.uint_to_t (uint_v start)) (U32.uint_to_t (uint_v n))

let disjoint #a1 #a2 #len1 #len2 b1 b2 = B.disjoint b1 b2

let live #a #len h b = B.live h b

let preserves_live h1 h2 =
  M.modifies M.address_liveness_insensitive_locs h1 h2

(* Converting between LSeq and F* sequences *)

let rec lseq_to_fstar_seq (#a: Type) (#len: size_nat) (s: LSeq.lseq a len) : Tot (FStar.Seq.seq a) =
  if len = 0
  then Seq.createEmpty
  else Seq.cons (LSeq.index s 0) (lseq_to_fstar_seq (LSeq.slice s 1 len))

assume val lseq_empty (a: Type) : LSeq.lseq a 0

assume val index_concat (#a: Type) (#len1 #len2: size_nat) (l1: LSeq.lseq a len1) (l2: LSeq.lseq a len2) (i: size_nat) : Lemma
  (requires (
    len1 + len2 <= maxint SIZE /\
    i < len1 + len2
  ))
  (ensures (
    LSeq.index (LSeq.concat l1 l2) i == (if i < len1 then LSeq.index l1 i else LSeq.index l2 (i - len1))
  ))

let rec fstar_seq_to_lseq (#a: Type) (len: size_nat) (s: Seq.seq a { Seq.length s == len } ) : Tot (LSeq.lseq a len) =
  if len = 0
  then lseq_empty a
  else LSeq.concat (LSeq.create 1 (Seq.head s)) (fstar_seq_to_lseq (len - 1) (Seq.tail s))

let as_seq #a #len b h = fstar_seq_to_lseq len (B.as_seq h b)

let as_lseq #a #len b h = as_seq b h

let modifies1 #a #len b h h' = M.modifies (M.loc_buffer b) h h'

let modifies2 #a1 #a2 #len1 #len2 b1 b2 h h' = M.modifies (M.loc_buffer b1 `M.loc_union` M.loc_buffer b2) h h'

let modifies3 #a1 #a2 #a3 #len1 #len2 #len3 b1 b2 b3 h h' = M.modifies (M.loc_buffer b1 `M.loc_union` M.loc_buffer b2 `M.loc_union` M.loc_buffer b3) h h'

let rec loc_of_list_bufitem (l: list bufitem) : GTot M.loc =
  match l with
  | [] -> M.loc_none
  | BufItem buf :: q -> M.loc_buffer buf `M.loc_union` loc_of_list_bufitem q

let modifies l h h' = M.modifies (loc_of_list_bufitem l) h h'

let rec live_list h l = match l with
  | [] -> True
  | BufItem buf :: q -> B.live h buf /\ live_list h q

let rec disjoint_list #a #len b l = match l with
  | [] -> True
  | BufItem buf :: q -> B.disjoint b buf /\ disjoint_list b q

let rec disjoint_lists l1 l2 = match l1 with
  | [] -> True
  | BufItem buf :: q -> disjoint_list buf l2 /\ disjoint_lists q l2

let disjoints l = match l with
  | [] -> True
  | BufItem buf :: q -> disjoint_list buf q

assume val uint32_to_fstar_uint32 (v: uint32) : Tot (v' : U32.t { uint_v v == U32.v v' } )

let sub #a #len #olen b start n =
  B.sub b (uint32_to_fstar_uint32 (size_to_uint32 start)) (uint32_to_fstar_uint32 (size_to_uint32 n))

let slice #a #len #olen b start fin =
  sub b start (fin `I.sub` start)

val index_fstar_seq_to_lseq
  (#a: Type)
  (len: size_nat)
  (s: Seq.seq a)
  (i: nat)
: Lemma
  (requires (Seq.length s == len /\ i < len))
  (ensures (LSeq.index (fstar_seq_to_lseq len s) i == Seq.index s i))
  [SMTPat (LSeq.index (fstar_seq_to_lseq len s) i)]

let rec index_fstar_seq_to_lseq #a len s i =
  index_concat (LSeq.create 1 (Seq.head s)) (fstar_seq_to_lseq (len - 1) (Seq.tail s)) i;
  if i = 0
  then ()
  else
    index_fstar_seq_to_lseq (len - 1) (Seq.tail s) (i - 1)

let index #a #len b i =
  B.index b (uint32_to_fstar_uint32 (size_to_uint32 i))

assume
val lseq_eq_intro
  (#a: Type)
  (#len: size_nat)
  (l1 l2: LSeq.lseq a len)
  (eq_index: (
    (i: size_nat) ->
    Lemma
    (requires (i < len))
    (ensures (LSeq.index l1 i == LSeq.index l2 i))
  ))
: Lemma
  (l1 == l2)

val fstar_seq_to_lseq_upd
  (#a: Type)
  (len: size_nat)
  (s: Seq.seq a)
  (i: nat)
  (x: a)
: Lemma
  (requires (Seq.length s == len /\ i < len))
  (ensures (fstar_seq_to_lseq len (Seq.upd s i x) == LSeq.upd (fstar_seq_to_lseq len s) i x))
  [SMTPat (fstar_seq_to_lseq len (Seq.upd s i x))]

let fstar_seq_to_lseq_upd #a len s i x =
  let s1 = fstar_seq_to_lseq len (Seq.upd s i x) in
  let s2 = LSeq.upd (fstar_seq_to_lseq len s) i x in
  lseq_eq_intro s1 s2
    (fun j -> if j = i then () else
      assert (LSeq.index s1 j == LSeq.index (fstar_seq_to_lseq len s) j)
    )

let upd #a #len b i x =
  B.upd b (uint32_to_fstar_uint32 (size_to_uint32 i)) x

assume
val fstar_seq_to_lseq_create
  (#a: Type)
  (len: size_nat)
  (init: a)
: Lemma
  (fstar_seq_to_lseq len (Seq.create len init) == LSeq.create len init)
  [SMTPat (fstar_seq_to_lseq len (Seq.create len init))]

inline_for_extraction
val create' 
  (#a:Type0)
  (#len:size_nat)
  (clen:size_t{v clen == len})
  (init:a)
: StackInline (lbuffer a len)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    preserves_live h0 h1 /\
    creates1 r h0 h1 /\
    modifies1 r h0 h1 /\
    as_seq  r h1 == LSeq.create #a (len) init /\
    (if B.g_is_null r then M.loc_buffer r == M.loc_none else B.frameOf r == HS.get_tip h0)
  ))

let create' #a #len clen init =
  if clen `I.eq` (I.nat_to_uint 0)
  then begin
    Classical.forall_intro_2 (fun t b -> B.disjoint_null a #t b);
    let h = HST.get () in
    assert (B.as_seq h B.null `Seq.equal` Seq.create 0 init);
    B.null
  end else
    B.alloca init (uint32_to_fstar_uint32 (size_to_uint32 clen))

let create #a #len clen init = create' clen init

let seq_length_of_list
  (#a: Type)
  (init: list a)
: Lemma
  (Seq.length (Seq.of_list init) == List.Tot.length init)
  [SMTPat (Seq.length (Seq.of_list init))]
= Seq.lemma_of_list_length (Seq.of_list init) init

assume
val fstar_seq_to_lseq_of_list
  (#a: Type)
  (init: list a)
: Lemma
  (requires (List.Tot.length init <= max_size_t))
  (ensures (
    fstar_seq_to_lseq (List.Tot.length init) (Seq.of_list init) == LSeq.createL init
  ))
  [SMTPat (fstar_seq_to_lseq (List.Tot.length init) (Seq.of_list init))]

let createL #a init =
  match init with
  | [] ->
    Classical.forall_intro_2 (fun t b -> B.disjoint_null a #t b);
    let h = HST.get () in
    assert (B.as_seq h (B.null #a) `Seq.equal` Seq.of_list init);
    B.null
  | _ ->
    B.alloca_of_list init

let modifies_none_creates1 (#a: Type) (#len: size_nat) (b: lbuffer a len) (h0 h1 h2: HS.mem) : Lemma
  (requires (M.modifies M.loc_none h0 h1 /\ creates1 b h1 h2))
  (ensures (creates1 b h0 h2))
= let g (a': Type) (len' : size_nat) (b' : lbuffer a' len') : Lemma
    (requires (live h0 b'))
    (ensures (live h1 b' /\ disjoint b b' /\ disjoint b' b))
  = ()
  in
  Classical.forall_intro_3 (fun a' len' b' -> Classical.move_requires (g a' len') b')

let alloc #h0 #a #b #w #len #wlen clen init write spec impl =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  M.fresh_frame_modifies h0 h1;
  let buf = create' clen init in
  let h = HST.get () in
  modifies_none_creates1 buf h0 h1 h;
  let res = impl buf in
  let hf = HST.get () in
  HST.pop_frame ();
  let h' = HST.get () in
  M.popped_modifies hf h';
  res

let alloc #h0 #a #b #w #len #wlen clen init_spec init write spec impl
