module Hacl.Impl.PQ.Lib

open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.Modifies
open Lib.ModifiesPat

module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module B   = Lib.Buffer
module Seq = Lib.Sequence

inline_for_extraction
type numeric_t = uint16

inline_for_extraction
let lbytes len = lbuffer uint8 (v len)

inline_for_extraction noextract
let v = size_v

inline_for_extraction
type matrix_t (n1:size_t) (n2:size_t{v n1 * v n2 < max_size_t}) = 
  lbuffer uint16 (v n1 * v n2)

val matrix_create:
  n1:size_t -> n2:size_t{0 < v n1 * v n2 /\ v n1 * v n2 < max_size_t} ->
  StackInline (matrix_t n1 n2)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    B.alloc_post_common (HS.get_tip h0) (v n1 * v n2) r h0 h1 /\
    B.as_seq h1 r == Seq.create (v n1 * v n2) (u16 0)))

[@ "substitute"]
let matrix_create n1 n2 =
  alloca #uint16 (u16 0) (n1 *. n2)

val lemma_matrix_index:
  n1:size_nat -> n2:size_nat ->
  i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (i * n2 + j < n1 * n2)
let lemma_matrix_index n1 n2 i j =
  assert (i * n2 + j <= (n1 - 1) * n2 + n2 - 1)

val mget:
  #n1:size_t -> #n2:size_t{v n1 * v n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} -> Stack uint16
  (requires (fun h -> B.live h a))
  (ensures (fun h0 r h1 -> h0 == h1)) ///\ r == Seq.index (B.as_seq h1 a) (v (i *. n2 +. j))))

[@ "substitute"]
let mget #n1 #n2 a i j =
  lemma_matrix_index (v n1) (v n2) (v i) (v j);
  a.(i *. n2 +. j)

val mset:
  #n1:size_t -> #n2:size_t{v n1 * v n2 < max_size_t} ->
  a:matrix_t n1 n2 ->
  i:size_t{v i < v n1} -> j:size_t{v j < v n2} ->
  vij:uint16 -> Stack unit
  (requires (fun h -> B.live h a))
  (ensures (fun h0 _ h1 -> B.live h1 a /\ modifies (loc_buffer a) h0 h1))

[@ "substitute"]
let mset #n1 #n2 a i j vij =
  lemma_matrix_index (v n1) (v n2) (v i) (v j);
  a.(i *. n2 +. j) <- vij

let loop_inv (#a:Type) (h0:HS.mem) (h1:HS.mem) 
  (len:size_nat) 
  (n:size_nat)
  (buf:lbuffer a len) 
  (i:size_nat{i <= n}) 
=
  B.live h0 buf /\ B.live h1 buf /\ modifies (loc_buffer buf) h0 h1

val matrix_add: 
    #n1:size_t -> #n2:size_t{v n1 * v n2 < max_size_t} 
  -> a:matrix_t n1 n2 
  -> b:matrix_t n1 n2 
  -> Stack unit
  (requires fun h -> B.live h a /\ B.live h b /\ B.disjoint a b)
  (ensures  fun h0 r h1 -> B.live h1 a /\ modifies (loc_buffer a) h0 h1)
[@"c_inline"]
let matrix_add #n1 #n2 a b =
  let h0 = ST.get () in
  let inv1 (h1:HS.mem) (j:nat{j <= v n1}) = loop_inv h0 h1 (v n1 * v n2) (v n1) a j in
  let inv2 (h1:HS.mem) (j:nat{j <= v n2}) = loop_inv h0 h1 (v n1 * v n2) (v n2) a j in
  Lib.Loops.for (size 0) n1 inv1 
  (fun i ->
    let h1 = ST.get () in
    Lib.Loops.for (size 0) n2 inv2
    (fun j ->
      let aij = mget a i j in
      let bij = mget b i j in
      let res = add_mod aij bij in
      mset a i j res
    )
  )

val matrix_sub:
    #n1:size_t 
  -> #n2:size_t{v n1 * v n2 < max_size_t} 
  -> a:matrix_t n1 n2 
  -> b:matrix_t n1 n2 
  -> Stack unit
  (requires fun h -> B.live h a /\ B.live h b /\ B.disjoint a b)
  (ensures  fun h0 r h1 -> B.live h1 b /\ modifies (loc_buffer b) h0 h1)
[@"c_inline"]
let matrix_sub #n1 #n2 a b =
  let h0 = ST.get () in
  let inv1 (h1:HS.mem) (j:nat{j <= v n1}) = loop_inv h0 h1 (v n1 * v n2) (v n1) b j in
  let inv2 (h1:HS.mem) (j:nat{j <= v n2}) = loop_inv h0 h1 (v n1 * v n2) (v n2) b j in
  Lib.Loops.for (size 0) n1 inv1
  (fun i ->
    let h1 = ST.get () in
    Lib.Loops.for (size 0) n2 inv2
    (fun j ->
      let aij = mget a i j in
      let bij = mget b i j in
      let res = sub_mod aij bij in
      mset b i j res
    )
  )

val matrix_mul:
    #n1:size_t 
  -> #n2:size_t{v n1 * v n2 < max_size_t} 
  -> #n3:size_t{v n2 * v n3 < max_size_t /\ v n1 * v n3 < max_size_t} 
  -> a:matrix_t n1 n2 
  -> b:matrix_t n2 n3 
  -> c:matrix_t n1 n3 
  -> Stack unit
  (requires fun h -> B.live h a /\ B.live h b /\ B.live h c 
    /\ B.disjoint a c /\ B.disjoint b c)
  (ensures (fun h0 _ h1 -> B.live h1 c /\ modifies (loc_buffer c) h0 h1))
[@"c_inline"]
let matrix_mul #n1 #n2 #n3 a b c =
  let h0 = ST.get () in
  let inv1 (h1:HS.mem) (j:nat{j <= v n1}) = loop_inv h0 h1 (v n1 * v n3) (v n1) c j in
  let inv2 (h1:HS.mem) (j:nat{j <= v n3}) = loop_inv h0 h1 (v n1 * v n3) (v n3) c j in
  let inv3 (h1:HS.mem) (j:nat{j <= v n2}) = loop_inv h0 h1 (v n1 * v n3) (v n2) c j in
  Lib.Loops.for (size 0) n1 inv1
  (fun i ->
    let h1 = ST.get () in
    Lib.Loops.for (size 0) n3 inv2
    (fun k ->
      mset c i k (u16 0);
      let h2 = ST.get () in
      Lib.Loops.for (size 0) n2 inv3
      (fun j ->
	let aij = mget a i j in
	let bjk = mget b j k in
	let cik = mget c i k in
	let res = cik +. aij *. bjk in
	mset c i k res
      )
    )
  )
