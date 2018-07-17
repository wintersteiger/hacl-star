module Lib.BufferOps

(* Handy notations for Lib.Buffer, so users can open this module
   instead of the whole Lib.Buffer, to just bring these operators
   and notations into the scope without bringing any definition from
   Lib.Buffer into the scope. *)

module HST = FStar.HyperStack.ST

module B   = Lib.Buffer
module Int = Lib.IntTypes
module Seq = Lib.Sequence
module M   = Lib.Modifies

inline_for_extraction unfold
let op_Array_Assignment #a l = B.upd #a l

inline_for_extraction unfold
let op_Array_Access #a l = B.index #a l

inline_for_extraction
val ( !* ) (#a: Type) (p: B.pointer a):
  HST.Stack a
  (requires (fun h -> B.live h p))
  (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0))

inline_for_extraction
val( *= ) (#a: Type) (p: B.pointer a) (v: a) : HST.Stack unit
  (requires (fun h -> B.live h p))
  (ensures (fun h0 _ h1 ->
    B.live h1 p /\
    B.as_seq h1 p `Seq.equal` Seq.create 1 v /\
    B.modifies_1 p h0 h1
  ))

unfold
let deref #a h (x:B.pointer a) =
  B.get h x 0

inline_for_extraction
val blit
  (#t: Type)
  (src: B.buffer t)
  (idx_src: Int.size_t)
  (dst: B.buffer t)
  (idx_dst: Int.size_t)
  (len: Int.size_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h src /\ B.live h dst /\ B.disjoint src dst /\
    Int.size_v idx_src + Int.size_v len <= B.length src /\
    Int.size_v idx_dst + Int.size_v len <= B.length dst
  ))
  (ensures (fun h _ h' ->
    M.modifies (M.loc_buffer dst) h h' /\
    B.live h' dst /\
    Seq.slice #_ #(B.length dst) (B.as_seq h' dst) (Int.size_v idx_dst) (Int.size_v idx_dst + Int.size_v len) ==
    Seq.slice #_ #(B.length src) (B.as_seq h src) (Int.size_v idx_src) (Int.size_v idx_src + Int.size_v len) /\
    Seq.slice #_ #(B.length dst) (B.as_seq h' dst) 0 (Int.size_v idx_dst) ==
    Seq.slice #_ #(B.length dst) (B.as_seq h dst) 0 (Int.size_v idx_dst) /\
    Seq.slice #_ #(B.length dst) (B.as_seq h' dst) (Int.size_v idx_dst + Int.size_v len) (B.length dst) ==
    Seq.slice #_ #(B.length dst) (B.as_seq h dst) (Int.size_v idx_dst + Int.size_v len) (B.length dst)
  ))
