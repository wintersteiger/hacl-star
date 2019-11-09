module Hacl.Impl.Blake2.Generic

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2_Vec

open Hacl.Impl.Blake2.Core

#set-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"




inline_for_extraction noextract
let rounds_t (a:Spec.alg): size_t = size (Spec.rounds a)

inline_for_extraction noextract
val size_to_word: al:Spec.alg -> s:size_t -> u:word_t al{u == Spec.nat_to_word al (v s)}
let size_to_word al s = match al with
  | Spec.Blake2S -> size_to_uint32 s
  | Spec.Blake2B -> size_to_uint64 s

inline_for_extraction noextract
val size_to_limb: al:Spec.alg -> s:size_t -> u:Spec.limb_t al{u == Spec.nat_to_limb al (v s)}
let size_to_limb al s = match al with
  | Spec.Blake2S -> size_to_uint64 s
  | Spec.Blake2B -> to_u128 (size_to_uint64 s)

/// Constants

let sigmaTable : x:ilbuffer Spec.sigma_elt_t 160ul{witnessed x Spec.sigmaTable /\ recallable x} =
  createL_global Spec.list_sigma

let ivTable_S: (x:ilbuffer (Spec.pub_word_t Spec.Blake2S) 8ul{witnessed x (Spec.ivTable Spec.Blake2S) /\ recallable x}) =
  createL_global Spec.list_iv_S

let ivTable_B: (x:ilbuffer (Spec.pub_word_t Spec.Blake2B) 8ul{witnessed x (Spec.ivTable Spec.Blake2B) /\ recallable x}) =
  createL_global Spec.list_iv_B

let rTable_S : x:ilbuffer (rotval U32) 4ul{witnessed x (Spec.rTable Spec.Blake2S) /\ recallable x} =
  createL_global Spec.rTable_list_S

let rTable_B : x:ilbuffer (rotval U64) 4ul{witnessed x (Spec.rTable Spec.Blake2B) /\ recallable x} =
  createL_global Spec.rTable_list_B


/// Accessors for constants

inline_for_extraction noextract
val get_iv:
  a:Spec.alg
  -> s: size_t{size_v s < 8} ->
  Stack (word_t a)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      v z == v (Seq.index (Spec.ivTable a) (v s))))

let get_iv a s =
  recall_contents #(Spec.pub_word_t Spec.Blake2S) #8ul ivTable_S (Spec.ivTable Spec.Blake2S);
  recall_contents #(Spec.pub_word_t Spec.Blake2B) #8ul ivTable_B (Spec.ivTable Spec.Blake2B);
  [@inline_let]
  let ivTable: (x:ilbuffer (Spec.pub_word_t a) 8ul{witnessed x (Spec.ivTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> ivTable_S
    | Spec.Blake2B -> ivTable_B
  in
  let r = index ivTable s in
  secret #(Spec.wt a) r


inline_for_extraction noextract
val get_sigma:
  s: size_t{v s < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ z == Lib.Sequence.(Spec.sigmaTable.[v s])))

let get_sigma s =
  recall_contents sigmaTable Spec.sigmaTable;
  index sigmaTable s


inline_for_extraction noextract
val get_sigma_sub:
  start: size_t ->
  i: size_t{v i < 16 /\ v start + v i < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.sigmaTable (v start + v i))))

let get_sigma_sub start i = get_sigma (start +. i)


inline_for_extraction noextract
val get_r:
  a: Spec.alg
  -> s: size_t{v s < 4} ->
  Stack (rotval (Spec.wt a))
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ z == Lib.Sequence.((Spec.rTable a).[v s])))

let get_r a s =
  recall_contents #(rotval (Spec.wt Spec.Blake2S)) #4ul rTable_S (Spec.rTable Spec.Blake2S);
  recall_contents #(rotval (Spec.wt Spec.Blake2B)) #4ul rTable_B (Spec.rTable Spec.Blake2B);
  let h0 = ST.get() in
  [@inline_let]
  let rTable: (x:ilbuffer (rotval (Spec.wt a)) 4ul{witnessed x (Spec.rTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> rTable_S
    | Spec.Blake2B -> rTable_B
  in
  index rTable s


/// Define algorithm functions

inline_for_extraction noextract
val g1: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t -> r:rotval (Spec.wt al) ->
  Stack unit
    (requires (fun h -> live h wv /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ (state_v h1 wv) == Spec.g1 al (state_v h0 wv) (v a) (v b) r))

let g1 #al #m wv a b r =
  let h0 = ST.get() in
  let wv_a = rowi wv a in
  let wv_b = rowi wv b in
  xor_row wv_a wv_b;
  ror_row wv_a r;
  let h2 = ST.get() in
  Lib.Sequence.eq_intro (state_v h2 wv) (Spec.g1 al (state_v h0 wv) (v a) (v b) r)



#push-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"
inline_for_extraction noextract
val g2: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t -> x:row_p al m ->
  Stack unit
    (requires (fun h -> live h wv /\ live h x /\ disjoint wv x /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.g2 al (state_v h0 wv) (v a) (v b) (row_v h0 x)))

let g2 #al #m wv a b x =
  let h0 = ST.get() in
  let wv_a = rowi wv a in
  let wv_b = rowi wv b in
  add_row wv_a wv_b;
  add_row wv_a x;
  let h1 = ST.get() in
  Lib.Sequence.eq_intro (state_v  h1 wv) (Spec.g2 al (state_v h0 wv) (v a) (v b) (row_v h0 x))

inline_for_extraction noextract
val blake2_mixing : #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> x:row_p al m -> y:row_p al m ->
  Stack unit
    (requires (fun h -> live h wv /\ live h x /\ live h y /\ disjoint wv x /\ disjoint wv y))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_mixing al (state_v h0 wv) (row_v h0 x) (row_v h0 y)))

let blake2_mixing #al #m wv x y =
  let h0 = ST.get() in
  push_frame ();
  let a = 0ul in
  let b = 1ul in
  let c = 2ul in
  let d = 3ul in
  let r0 = get_r al (size 0) in
  let r1 = get_r al (size 1) in
  let r2 = get_r al (size 2) in
  let r3 = get_r al (size 3) in
  let zz = alloc_row al m in
  let h1 = ST.get() in
  g2 wv a b x;
  g1 wv d a r0;
  g2 wv c d zz;
  g1 wv b c r1;
  g2 wv a b y;
  g1 wv d a r2;
  g2 wv c d zz;
  g1 wv b c r3;
  let h2 = ST.get() in
  pop_frame ();
  let h3 = ST.get() in
  assert(modifies (loc wv) h0 h3);
  Lib.Sequence.eq_intro (state_v h2 wv) (Spec.blake2_mixing al (state_v h1 wv) (row_v h1 x) (row_v h1 y))
#pop-options

inline_for_extraction noextract
val diag: #a:Spec.alg -> #m:m_spec -> wv:state_p a m
	  -> ST unit
	    (requires (fun h -> live h wv))
	    (ensures (fun h0 _ h1 -> modifies (loc wv) h0 h1 /\
				  state_v h1 wv == Spec.diag (state_v h0 wv)))
let diag #a #m wv =
  let r1 = rowi wv 1ul in
  let r2 = rowi wv 2ul in
  let r3 = rowi wv 3ul in
  let h0 = ST.get() in
  permr_row r1 1ul;
  permr_row r2 2ul;
  permr_row r3 3ul


inline_for_extraction noextract
val undiag: #a:Spec.alg -> #m:m_spec -> wv:state_p a m
	  -> ST unit
	    (requires (fun h -> live h wv))
	    (ensures (fun h0 _ h1 -> modifies (loc wv) h0 h1 /\
				  state_v h1 wv == Spec.undiag (state_v h0 wv)))
let undiag #a #m wv =
  let r1 = rowi wv 1ul in
  let r2 = rowi wv 2ul in
  let r3 = rowi wv 3ul in
  let h0 = ST.get() in
  permr_row r1 3ul;
  permr_row r2 2ul;
  permr_row r3 1ul


inline_for_extraction
val gather_state: #a:Spec.alg -> #ms:m_spec -> st:state_p a ms -> m:lbuffer uint8 (size_block a) -> start:size_t{v start <= 144} -> ST unit
		  (requires (fun h -> live h st /\ live h m /\ disjoint st m))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
					state_v h1 st == Spec.gather_state a (as_seq h0 m) (v start)))

#push-options "--z3rlimit 100"
let gather_state #a #ms st m start =
  let h0 = ST.get() in
  let r0 = rowi st 0ul in
  let r1 = rowi st 1ul in
  let r2 = rowi st 2ul in
  let r3 = rowi st 3ul in
  let s0 = get_sigma start in
  let s1 = get_sigma (start +. 1ul) in
  let s2 = get_sigma (start +. 2ul) in
  let s3 = get_sigma (start +. 3ul) in
  let s4 = get_sigma (start +. 4ul) in
  let s5 = get_sigma (start +. 5ul) in
  let s6 = get_sigma (start +. 6ul)in
  let s7 = get_sigma (start +. 7ul) in
  let s8 = get_sigma (start +. 8ul) in
  let s9 = get_sigma (start +. 9ul) in
  let s10 = get_sigma (start +. 10ul) in
  let s11 = get_sigma (start +. 11ul) in
  let s12 = get_sigma (start +. 12ul) in
  let s13 = get_sigma (start +. 13ul) in
  let s14 = get_sigma (start +. 14ul) in
  let s15 = get_sigma (start +. 15ul) in
  let h1 = ST.get() in
  gather_row r0 m s0 s2 s4 s6;
  let h2 = ST.get() in
  gather_row r1 m s1 s3 s5 s7;
  let h3 = ST.get() in
  gather_row r2 m s8 s10 s12 s14;
  let h4 = ST.get() in
  gather_row r3 m s9 s11 s13 s15;
  let h5 = ST.get() in
  assert(modifies (loc st) h0 h5);
  Lib.Sequence.eq_intro (state_v h5 st) (Spec.gather_state a (as_seq h0 m) (v start))

inline_for_extraction noextract
val blake2_round : #al:Spec.alg -> #ms:m_spec -> wv:state_p al ms ->  m:lbuffer uint8 (size_block al) -> i:size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_round al (as_seq h0 m) (v i) (state_v h0 wv)))

let blake2_round #al #ms wv m i =
  push_frame();
  let start_idx = (i %. size 10) *. size 16 in
  assert (v start_idx == (v i % 10) * 16);
  assert (v start_idx <= 144);
  let m_st = alloc_state al ms in
  gather_state m_st m start_idx;
  let x = rowi m_st 0ul in
  let y = rowi m_st 1ul in
  let z = rowi m_st 2ul in
  let w = rowi m_st 3ul in
  let h1 = ST.get() in
  assert (disjoint wv m_st);
  assert (disjoint m_st wv);
  assert (disjoint x wv);
  assert (disjoint wv x);
  assert (disjoint y wv);
  assert (disjoint wv y);
  assert (disjoint z wv);
  assert (disjoint wv z);
  assert (disjoint w wv);
  assert (disjoint wv w);
  blake2_mixing wv x y;
  diag  wv;
  blake2_mixing wv z w;
  undiag wv;
  pop_frame ()

inline_for_extraction noextract
val blake2_compress1:
    #al:Spec.alg
  -> #m:m_spec
  -> wv: state_p al m
  -> s_iv: state_p al m
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h wv /\ live h s_iv /\ disjoint wv s_iv))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_compress1 al (state_v h0 s_iv) offset flag))

let blake2_compress1 #al #m wv s_iv offset flag =
  let h0 = ST.get() in
  push_frame();
  let mask = alloc_row al m in
  [@inline_let]
  let wv_12 = Spec.limb_to_word al offset in
  [@inline_let]
  let wv_13 = Spec.limb_to_word al (offset >>. (size (bits (Spec.wt al)))) in
  let wv_14 = if flag then ones (Spec.wt al) SEC else (Spec.zero al) in
  let wv_15 = Spec.zero al in
  create_row mask wv_12 wv_13 wv_14 wv_15;
  copy_state wv s_iv;
  let wv3 = rowi wv 3ul in
  xor_row wv3 mask;
  pop_frame();
  let h1 = ST.get() in
  assert(modifies (loc wv) h0 h1);
  Lib.Sequence.eq_intro (state_v h1 wv) (Spec.blake2_compress1 al (state_v h0 s_iv) offset flag);
  admit()


inline_for_extraction noextract
val blake2_compress2 :
  al:Spec.alg
  -> wv: vector_wp al
  -> m: block_wp al ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[|wv|] == Spec.blake2_compress2 al h0.[|wv|] h0.[|m|]))

let blake2_compress2 al wv m =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.blake2_round al h.[|m|] in
  loop1 h0 (rounds_t al) wv spec
  (fun i ->
    Loops.unfold_repeati (Spec.rounds al) (spec h0) h0.[|wv|] (v i);
    blake2_round al wv m i)


inline_for_extraction noextract
val blake2_compress3_inner :
  al:Spec.alg
  -> wv: vector_wp al
  -> i: size_t{v i < 8}
  -> s: hash_wp al ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                   /\ disjoint s wv /\ disjoint wv s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress3_inner al h0.[|wv|] (v i) h0.[|s|]))

let blake2_compress3_inner al wv i s =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  let hi = logxor hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


inline_for_extraction noextract
val blake2_compress3 :
  al:Spec.alg
  -> wv: vector_wp al
  -> s: hash_wp al ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                     /\ disjoint wv s /\ disjoint s wv))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress3 al h0.[|wv|] h0.[|s|]))

let blake2_compress3 al wv s =
  [@inline_let]
  let spec h = Spec.blake2_compress3_inner al h.[|wv|] in
  let h0 = ST.get () in
  loop1 h0 (size 8) s
    (fun h -> spec h)
    (fun i ->
      Loops.unfold_repeati 8 (spec h0) (as_seq h0 s) (v i);
      blake2_compress3_inner al wv i s)


inline_for_extraction noextract
let compress_t (al:Spec.alg) =
    s: hash_wp al
  -> m: block_wp al
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m
                     /\ disjoint s m /\ disjoint m s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[|s|] == Spec.blake2_compress al h0.[|s|] h0.[|m|] offset flag))


inline_for_extraction noextract
val blake2_compress: al:Spec.alg -> compress_t al


let blake2_compress al s m offset flag =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 s /\ h1.[|s|] == Spec.blake2_compress al h0.[|s|] h0.[|m|] offset flag in
  salloc1 h0 (size 16) (Spec.nat_to_word al 0) (Ghost.hide (loc s)) spec
  (fun wv ->
    blake2_compress1 al wv s m offset flag;
    blake2_compress2 al wv m;
    blake2_compress3 al wv s)


inline_for_extraction noextract
let blake2_update_block_t
    (al:Spec.alg) =
    hash: hash_wp al
  -> flag: bool
  -> totlen: Spec.limb_t al{v totlen <= Spec.max_limb al}
  -> d: block_p al ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.blake2_update_block al flag (v totlen) h0.[|d|] h0.[|hash|]))


inline_for_extraction noextract
val blake2_update_block: (al:Spec.alg) -> blake2_compress: compress_t al -> blake2_update_block_t al

let blake2_update_block al blake2_compress hash flag totlen d =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = live h1 hash /\ h1.[|hash|] == Spec.blake2_update_block al flag (v totlen) h0.[|d|] h0.[|hash|] in
  salloc1 h0 (size 16) (Spec.nat_to_word al 0) (Ghost.hide (loc hash)) spec
  (fun block_w ->
     uints_from_bytes_le block_w d;
     let offset = totlen in
     blake2_compress hash block_w offset flag)



inline_for_extraction noextract
val blake2_init_hash:
    al:Spec.alg
  -> hash: hash_wp al
  -> kk: size_t{v kk <= Spec.max_key al}
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
     (requires (fun h -> live h hash))
     (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                          /\ h1.[|hash|] == Spec.blake2_init_hash al (v kk) (v nn)))

let blake2_init_hash al hash kk nn =
  set_iv al hash;
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left (size_to_word al kk) (size 8) in
  let s0' = s0 ^. (Spec.nat_to_word al 0x01010000) ^. kk_shift_8 ^. (size_to_word al nn) in
  hash.(size 0) <- s0'


inline_for_extraction noextract
let blake2_init_branching_t
    (al:Spec.alg) =
    hash: hash_wp al
  -> key_block: lbuffer uint8 (size_block al)
  -> kk: size_t{v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h k /\ live h key_block
                   /\ disjoint hash k /\ disjoint hash key_block /\ disjoint key_block k))
    (ensures  (fun h0 _ h1 -> modifies2 hash key_block h0 h1
                    /\ (if (v kk) = 0 then h1.[|hash|] == h0.[|hash|] else
                       let key_block1: Spec.block_s al = Seq.update_sub h0.[|key_block|] 0 (v kk) h0.[|k|] in
                       h1.[|hash|] == Spec.blake2_update_block al false (Spec.size_block al) key_block1 h0.[|hash|])))


inline_for_extraction noextract
val blake2_init_branching: al:Spec.alg -> blake2_update_block_t al -> blake2_init_branching_t al

let blake2_init_branching al blake2_update_block hash key_block kk k nn =
  let h0 = ST.get () in
  if kk <>. (size 0) then
  begin
    update_sub key_block (size 0) kk k;
    assert(v (secret (size_block al)) <= Spec.max_limb al);
    let totlenw = size_to_word al (size_block al) in
    [@inline_let]
    let totlen = Spec.word_to_limb al totlenw in
    blake2_update_block hash false totlen key_block
  end


inline_for_extraction noextract
let blake2_init_t
    (al:Spec.alg) =
    hash: hash_wp al
  -> kk: size_t{v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.blake2_init al (v kk) h0.[|k|] (v nn)))

inline_for_extraction noextract
val blake2_init: al:Spec.alg -> blake2_update_block_t al -> blake2_init_t al

let blake2_init al blake2_update_block hash kk k nn =
  let h0 = ST.get () in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash))
  (fun _ h1 -> live h1 hash /\ h1.[|hash|] == Spec.blake2_init al (v kk) h0.[|k|] (v nn))
  (fun key_block ->
    blake2_init_hash al hash kk nn;
    blake2_init_branching al blake2_update_block hash key_block kk k nn)


#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
let _ : squash (inversion Spec.alg) = allow_inversion Spec.alg


inline_for_extraction noextract
val blake2_update_block_multi_step:
    al:Spec.alg
  -> blake2_update_block:blake2_update_block_t al
  -> hash: hash_wp al
  -> prev: Spec.limb_t al
  -> n: size_t{v prev + v n * (Spec.size_block al) <= Spec.max_limb al /\ v n * (Spec.size_block al) <= max_size_t}
  -> i: size_t{v i < v n}
  -> blocks: lbuffer uint8 (n *! size_block al){v n * (Spec.size_block al) = length blocks} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h blocks /\ disjoint hash blocks))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1 /\
                           max_size_t <= Spec.max_limb al /\
                           h1.[|hash|] == Spec.blake2_update_block_multi_step al (v prev) (v n) h0.[|blocks|] (v i) h0.[|hash|]))

let blake2_update_block_multi_step al blake2_update_block hash prev n i blocks =
  let curlen:size_t = (i +! 1ul) *! (size_block al) in
  let curlen:Spec.limb_t al = size_to_limb al curlen in
  let totlen:Spec.limb_t al = prev +! curlen in
  let block:block_p al = sub blocks (i *! (size_block al)) (size_block al) in
  blake2_update_block hash false totlen block

#pop-options


inline_for_extraction noextract
let blake2_update_block_multi_t
    (al:Spec.alg) =
    hash: hash_wp al
  -> prev: Spec.limb_t al
  -> n: size_t{v prev + v n * (Spec.size_block al) <= Spec.max_limb al /\ v n * (Spec.size_block al) <= max_size_t}
  -> blocks: lbuffer uint8 (n *! (size_block al)) ->
  Stack unit
    (requires (fun h -> live h hash /\ live h blocks /\ disjoint hash blocks))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                        /\ h1.[|hash|] == Spec.blake2_update_block_multi al (v prev) (v n) h0.[|blocks|] h0.[|hash|]))

inline_for_extraction noextract
val blake2_update_block_multi: al:Spec.alg -> blake2_update_block_t al -> blake2_update_block_multi_t al

let blake2_update_block_multi al blake2_update_block hash prev n blocks =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.blake2_update_block_multi_step al (v prev) (v n) h0.[|blocks|] in
  loop1 h0 n hash spec
  (fun i ->
    Loops.unfold_repeati (v n) (spec h0) h0.[|hash|] (v i);
    blake2_update_block_multi_step al blake2_update_block hash prev n i blocks)


inline_for_extraction noextract
let blake2_update_last_t
    (al:Spec.alg) =
    hash: hash_wp al
  -> prev: Spec.limb_t al
  -> rem: size_t{v rem <= Spec.size_block al /\ v prev + v rem <= Spec.max_limb al}
  -> last: lbuffer uint8 rem ->
  Stack unit
    (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[|hash|] == Spec.blake2_update_last al (v prev) (v rem) h0.[|last|] h0.[|hash|]))

inline_for_extraction noextract
val blake2_update_last: al:Spec.alg -> blake2_update_block_t al -> blake2_update_last_t al

let blake2_update_last al blake2_update_block hash prev rem last =
  let h0 = ST.get () in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash))
  (fun _ h1 -> live h1 hash /\ h1.[|hash|] == Spec.blake2_update_last al (v prev) (v rem) h0.[|last|] h0.[|hash|])
  (fun last_block ->
    update_sub last_block (size 0) rem last;
    let totlen: Spec.limb_t al = prev +! (size_to_limb al rem) in
    blake2_update_block hash true totlen last_block)


inline_for_extraction noextract
let blake2_finish_t
    (al:Spec.alg) =
    nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> hash: hash_wp al ->
  Stack unit
    (requires (fun h -> live h hash /\ live h output /\ disjoint output hash))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|output|] == Spec.blake2_finish al h0.[|hash|] (v nn)))

inline_for_extraction noextract
val blake2_finish:al:Spec.alg -> blake2_finish_t al

let blake2_finish al nn output hash =
  let h0 = ST.get () in
  salloc1 h0 (size (Spec.max_output al)) (u8 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[|output|] == Spec.blake2_finish al h0.[|hash|] (v nn))
  (fun full ->
    uints_to_bytes_le (size 8) full hash;
    let final = sub full (size 0) nn in
    copy output final)



inline_for_extraction noextract
val compute_prev_multi:
    al:Spec.alg
  -> kn:size_t{v kn == 0 \/ v kn == 1} ->
  Tot (r:Spec.limb_t al{v r = (v kn) * Spec.size_block al})

let compute_prev_multi al kn =
  size_to_limb al (kn *! (size_block al))


inline_for_extraction noextract
val compute_prev_last:
    al:Spec.alg
  -> prev_multi:Spec.limb_t al{v prev_multi == 0 \/ v prev_multi == Spec.size_block al}
  -> n: size_t{v prev_multi + (v n) * (Spec.size_block al) <= max_size_t}
  -> rem: size_t ->
  Tot (r:Spec.limb_t al)

let compute_prev_last al prev_multi n rem =
  prev_multi +! (size_to_limb al (n *! (size_block al)))


val lemma_prev_last:
    al:Spec.alg
  -> prev_multi:Spec.limb_t al{v prev_multi == 0 \/ v prev_multi == Spec.size_block al}
  -> n: size_t{v prev_multi + (v n) * (Spec.size_block al) <= max_size_t}
  -> rem: size_t ->
  Lemma (ensures(
    let r = compute_prev_last al prev_multi n rem in
    v r = v prev_multi + (v n) * Spec.size_block al /\ v r + v rem <= Spec.max_limb al))
  [SMTPat (compute_prev_last al prev_multi n rem)]

let lemma_prev_last al prev_multi n rem = ()


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0"
let _ : squash (inversion Spec.alg) = allow_inversion Spec.alg


noextract
val lemma_spec_blake2:
    h0:mem
  -> al:Spec.alg
  -> nn:size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= Spec.max_key al /\ (if v kk = 0 then v ll <= max_size_t else v ll + Spec.size_block al <= max_size_t)}
  -> k: lbuffer uint8 kk ->
  Lemma (
    let n0 = ll /. (size_block al) in
    let rem0 = ll %. (size_block al) in
    let kn = if kk =. 0ul then 0ul else 1ul in
    let n = if n0 <>. 0ul && rem0 =. 0ul then n0 -! 1ul else n0 in
    let rem = if n0 <>. 0ul && rem0 =. 0ul then size_block al else rem0 in
    let prev_multi: Spec.limb_t al = compute_prev_multi al kn in
    let prev_last: Spec.limb_t al = compute_prev_last al prev_multi n rem in
    let blocks = gsub d 0ul (n *! (size_block al)) in
    let last = gsub d (n *! (size_block al)) rem in
    let spec_blocks = Seq.slice #uint8 #(v ll) h0.[|d|] 0 (v n * Spec.size_block al) in
    let spec_last = Seq.slice #uint8 #(v ll) h0.[|d|] (v n * Spec.size_block al) (v ll) in
    let hash1 = Spec.blake2_init al (v kk) h0.[|k|] (v nn) in
    let hash2 = Spec.blake2_update_block_multi al (v prev_multi) (v n) h0.[|blocks|] hash1 in
    let hash3 = Spec.blake2_update_last al (v prev_last) (v rem) h0.[|last|] hash2 in
    let spec_output = Spec.blake2_finish al hash3 (v nn) in
    spec_output == Spec.blake2 al h0.[|d|] (v kk) h0.[|k|] (v nn))

let lemma_spec_blake2 h0 al nn output ll d kk k = ()


inline_for_extraction noextract
let blake2_t (al:Spec.alg) =
    nn:size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= Spec.max_key al /\ (if v kk = 0 then v ll <= max_size_t else v ll + Spec.size_block al <= max_size_t)}
  -> k: lbuffer uint8 kk ->
  Stack unit
    (requires (fun h -> live h output /\ live h d /\ live h k
                   /\ disjoint output d /\ disjoint output k /\ disjoint d k))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|output|] == Spec.blake2 al h0.[|d|] (v kk) h0.[|k|] (v nn)))


inline_for_extraction noextract
val blake2: al:Spec.alg ->
  blake2_init_t al -> blake2_update_block_multi_t al -> blake2_update_last_t al -> blake2_finish_t al -> blake2_t al

let blake2 al blake2_init blake2_update_block_multi blake2_update_last blake2_finish nn output ll d kk k =
  let h00 = ST.get () in
  let n0 = ll /. (size_block al) in
  let rem0 = ll %. (size_block al) in
  let kn = if kk =. 0ul then 0ul else 1ul in
  let n = if n0 <>. 0ul && rem0 =. 0ul then n0 -! 1ul else n0 in
  let rem = if n0 <>. 0ul && rem0 =. 0ul then size_block al else rem0 in
  let h01 = ST.get () in
  let blocks = sub d 0ul (n *! (size_block al)) in
  let last = sub d (n *! (size_block al)) rem in
  let prev_multi: Spec.limb_t al = compute_prev_multi al kn in
  let prev_last: Spec.limb_t al = compute_prev_last al prev_multi n rem in
  let h01 = ST.get () in
  salloc1 h01 (size 8) (Spec.nat_to_word al 0) (Ghost.hide (loc output))
  (fun _ h1 -> live h1 output /\ h1.[|output|] == Spec.blake2 al h01.[|d|] (v kk) h01.[|k|] (v nn))
  (fun hash ->
    blake2_init hash kk k nn;
    blake2_update_block_multi hash prev_multi n blocks;
    blake2_update_last hash prev_last rem last;
    blake2_finish nn output hash;
    lemma_spec_blake2 h01 al nn output ll d kk k
  )