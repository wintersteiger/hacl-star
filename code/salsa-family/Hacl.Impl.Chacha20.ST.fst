module Hacl.Impl.Chacha20.ST

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20.ST
open C.Loops
open Hacl.Lib.LoadStore32

module Spec = Spec.Chacha20.ST

module U32 = FStar.UInt32
module H8  = FStar.UInt8
module H32 = FStar.UInt32

let u32 = U32.t
let h32 = U32.t
let h8 = H8.t
let uint8_p = buffer H8.t


#reset-options "--max_fuel 0 --z3rlimit 50"
type state = b:Buffer.buffer h32{length b = 16}

[@ "c_inline"]
private let rotate_left (a:h32) (s:u32{0 < U32.v s /\ U32.v s < 32}) : Tot h32 = 
  Spec.Lib.rotate_left a s

private inline_for_extraction let ( <<< ) = rotate_left

let idx = a:U32.t{U32.v a < 16}

let idx_v (i:idx) : (Spec.idx) = U32.v i
let st_v (s:Seq.seq h32{Seq.length s = 16}) : (Spec.st) = s

let state_pre (st:state) h0 = live h0 st
let state_post (spec:Spec.chacha_st 'b) (st:state) h0 r h1 = 
	       live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\ 
	       spec (st_v (as_seq h0 st)) == 
	            (r,st_v (as_seq h1 st))

#reset-options "--max_fuel 0 --z3rlimit 50"
noeq
type stateful_st 'b = 
   | MkStateful: 
     spec:Spec.chacha_st 'b -> 
     impl: (st:state -> Stack 'b
              (requires (fun h -> state_pre st h))
	      (ensures  (fun h0 r h1 -> state_post spec st h0 r h1))) ->
     stateful_st 'b
     
unfold
let read_st (i:idx) : stateful_st h32 = MkStateful (Spec.read (idx_v i)) (fun st -> st.(i))

unfold
let write_st (i:idx) (v:h32) : stateful_st unit = MkStateful (Spec.write (idx_v i) v) (fun st -> st.(i) <- v)

#reset-options "--max_fuel 0 --z3rlimit 50"
unfold
let bind #a #b (f:stateful_st a) (g:a -> stateful_st b) = 
  MkStateful (Spec.bind f.spec (fun x -> (g x).spec))
    (fun st -> let r = f.impl st in
  	    (g r).impl st)

let return (a:'a) : stateful_st 'a = 
    MkStateful (fun st -> a,st)
	       (fun st -> a)

assume val iter: c:u32 -> spec: Spec.chacha_st unit -> f:stateful_st unit{forall st. f.spec st = spec st} ->
	  Tot (r:stateful_st unit {
		forall st. r.spec st = Spec.iter (U32.v c) spec st})

#reset-options "--max_fuel 0 --z3rlimit 10"
[@ "substitute"]
private
val line:
  a:idx -> b:idx -> d:idx -> s:U32.t{0 < U32.v s /\ U32.v s < 32} ->
  Tot (r:stateful_st unit{forall st. r.spec st == Spec.line (idx_v a) (idx_v b) (idx_v d) s st})
[@ "substitute"]
let line a b d s = 
  sa <-- read_st a ;
  sb <-- read_st b ;
  write_st a (sa +%^ sb) ;;
  sa <-- read_st a ;
  sd <-- read_st d ;
  write_st d ((sd ^^ sa) <<< s)

let sh16: s:U32.t{0 < U32.v s /\ U32.v s < 32} = 16ul
let sh12: s:U32.t{0 < U32.v s /\ U32.v s < 32} = 12ul
let sh8: s:U32.t{0 < U32.v s /\ U32.v s < 32} = 8ul
let sh7: s:U32.t{0 < U32.v s /\ U32.v s < 32} = 7ul

#reset-options "--max_fuel 0 --z3rlimit 300"

(* EXPENSIVE 145s *)
[@ "c_inline"]
private
val quarter_round:
  a:idx -> b:idx -> c:idx -> d:idx ->
  Tot (r:stateful_st unit{forall st. r.spec st == Spec.quarter_round (idx_v a) (idx_v b) (idx_v c) (idx_v d) st})
[@ "c_inline"]
let quarter_round a b c d =
  line a b d sh16;;
  line c d b sh12;;
  line a b d sh8 ;;
  line c d b sh7

(* MOST EXPENSIVE SO FAR 100s *)
[@ "substitute"]
private
val column_round: (r:stateful_st unit{forall st. r.spec st == Spec.column_round st})
[@ "substitute"]
let column_round =
  quarter_round 0ul 4ul 8ul  12ul;;
  quarter_round 1ul 5ul 9ul  13ul;;
  quarter_round 2ul 6ul 10ul 14ul;;
  quarter_round 3ul 7ul 11ul 15ul

[@ "substitute"]
private
val diagonal_round: (r:stateful_st unit{forall st. r.spec st == Spec.diagonal_round st})
[@ "substitute"]
let diagonal_round =
  quarter_round 0ul 5ul 10ul 15ul;;
  quarter_round 1ul 6ul 11ul 12ul;;
  quarter_round 2ul 7ul 8ul  13ul;;
  quarter_round 3ul 4ul 9ul  14ul


[@ "c_inline"]
private
val double_round: (r:stateful_st unit{forall st. r.spec st == Spec.double_round st})
[@ "c_inline"]
let double_round =
    column_round ;;
    diagonal_round 

[@ "c_inline"]
val rounds:  (r:stateful_st unit{forall st. r.spec st == Spec.rounds st})
[@ "c_inline"]
let rounds =
   iter 10ul Spec.double_round double_round


assume val uint32s_from_le: src:buffer h8 -> start:idx -> 
			    len:u32{FStar.Mul.(U32.v len * 4 = Buffer.length src)  
			            /\ U32.v start + U32.v len <= 16} -> 
			    st: state -> 
			    Stack unit
			    (requires (fun h -> state_pre st h /\ live h src))
			    (ensures  (fun h0 r h1 -> 
					 live h0 src /\ live h1 src /\
					 (let spec = Spec.uint32s_from_le 
						    (as_seq h0 src) (idx_v start) (U32.v len) in 
					  state_post spec st h0 r h1)))

  
#reset-options "--max_fuel 0 --z3rlimit 100"
let setup0 (c:U32.t) : (s:stateful_st unit{
	     forall st. s.spec st == Spec.setup0 (U32.v c) st}) =
   write_st 0ul 0x61707865ul;;
   write_st 1ul 0x3320646eul;;
   write_st 2ul 0x79622d32ul;;
   write_st 3ul 0x6b206574ul;;
   write_st 12ul c 

(* EXPENSIVE 85s *)
val setup1: k:uint8_p{length k = 32} ->
            n:uint8_p{length n = 12} ->
           st: state -> 
           Stack unit
           (requires (fun h -> state_pre st h /\ live h k /\ live h n /\  
			    disjoint st k /\ disjoint st n))
           (ensures  (fun h0 r h1 -> live h0 k /\ live h0 n /\
   			          live h1 k /\ live h1 n /\
		           (let spec = Spec.setup1 (as_seq h0 k) (as_seq h0 n) in
			    state_post spec st h0 r h1)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let setup1 k n st = 
  uint32s_from_le k 4ul 8ul st;
  uint32s_from_le n 13ul 3ul st


val setup: k:uint8_p{length k = 32} ->
           n:uint8_p{length n = 12} ->
	   c:U32.t ->
           st: state -> 
           Stack unit
           (requires (fun h -> state_pre st h /\ live h k /\ live h n /\  
			    disjoint st k /\ disjoint st n))
           (ensures  (fun h0 r h1 -> live h0 k /\ live h0 n /\
   			          live h1 k /\ live h1 n /\
		           (let spec = Spec.setup (as_seq h0 k) (as_seq h0 n) 
			                          (U32.v c) in
			    state_post spec st h0 r h1)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let setup k n c st = 
  let s0 = setup0 c in
  s0.impl st;
  setup1 k n st




#reset-options " --max_fuel 0 --z3rlimit 100"
[@ "c_inline"]
val sum_states:
  st_in:state ->
  st_out:state ->
  Stack unit
    (requires (fun h -> state_pre st_out h /\ live h st_in /\ disjoint st_in st_out))
    (ensures  (fun h0 r h1 -> live h0 st_in /\ live h1 st_in /\
        (let spec = Spec.in_place_map2 (+%^) (as_seq h0 st_in) in
	 state_post spec st_out h0 r h1)))
[@ "c_inline"]
let sum_states st_in st_out =
  in_place_map2 st_out st_in 16ul (fun x y -> H32.(x +%^ y))


[@ "c_inline"]
val copy_state:
  st_in:state ->
  st_out:state ->
  Stack unit
    (requires (fun h -> state_pre st_out h /\ live h st_in /\ disjoint st_in st_out))
    (ensures (fun h0 r h1 -> live h0 st_in /\ live h1 st_in /\ 
      live h0 st_out /\ live h1 st_out /\ modifies_1 st_out h0 h1 /\
      (as_seq h0 st_in) == (as_seq h1 st_out)))
[@ "c_inline"]
let copy_state st_in st_out =
  Buffer.blit st_in 0ul st_out 0ul 16ul

	
#reset-options " --max_fuel 0 --z3rlimit 300"

[@ "c_inline"]
private
val chacha20_core:
  st_copy:state ->
  st:state ->
  Stack unit
    (requires (fun h -> state_pre st h /\ live h st_copy /\ disjoint st st_copy))
    (ensures  (fun h0 r h1 -> live h0 st_copy /\ live h1 st_copy /\ modifies_2 st st_copy h0 h1 /\ 
     live h0 st /\ live h1 st /\ 
     Spec.chacha20_core (as_seq h0 st) == (r,as_seq h1 st)))
[@ "c_inline"]
let chacha20_core st st_copy =
  let h0 = ST.get() in
  copy_state st st_copy;
  let h1 = ST.get() in
  assert (as_seq h1 st_copy == as_seq h0 st);
  assert (as_seq h1 st == as_seq h0 st);
  rounds.impl st;
  let h2 = ST.get() in
  assert (((),as_seq h2 st) == Spec.rounds (as_seq h1 st));
  assert (as_seq h2 st_copy == as_seq h1 st_copy);
  sum_states st_copy st;
  let h3 = ST.get() in
  assert (((),as_seq h3 st) == Spec.in_place_map2 (+%^) (as_seq h2 st_copy) (as_seq h2 st));
  assert (modifies_2 st st_copy h0 h3);
  assert (((),as_seq h3 st) == Spec.in_place_map2 (+%^) (as_seq h0 st) (snd (Spec.rounds (as_seq h0 st))));
//  assert (((),as_seq h3 st) == Spec.chacha20_core (as_seq h0 st));
  admit()


(*
#reset-options " --max_fuel 0 --z3rlimit 100"

type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> log_t_
type log_t = Ghost.erased log_t_


(* Invariant on the state recording which block was computed last *)
let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s   = as_seq h st in
    match log with | MkLog key nonce -> 
       forall st.
	((),reveal_h32s s) == 
	Spec.setup key nonce (H32.v (Seq.index s 12)) st)


private
val lemma_invariant:
  st:Spec.state ->
  k:Spec.key -> n:Spec.nonce -> c:H32.t -> c':H32.t -> Lemma
    (requires (st == Spec.setup k n (H32.v c)))
    (ensures (Seq.upd st 12 (h32_to_u32 c') == Spec.setup k n (H32.v c')))
let lemma_invariant s k n c c' =
  let s' = Seq.upd s 12 (h32_to_u32 c') in
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Seq.slice s' 4 12);
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Seq.slice s' 13 16);
  Seq.lemma_eq_intro (Seq.slice s 4 12) (Spec.Lib.uint32s_from_le 8 k);
  Seq.lemma_eq_intro (Seq.slice s' 4 12) (Spec.Lib.uint32s_from_le 8 k);
  Seq.lemma_eq_intro (Seq.slice s 13 16) (Spec.Lib.uint32s_from_le 3 n);
  Seq.lemma_eq_intro (Seq.slice s' 13 16) (Spec.Lib.uint32s_from_le 3 n);
  cut (h32_to_u32 c == (Seq.index (Seq.slice s 12 13) 0));
  cut (h32_to_u32 c' == (Seq.index (Seq.slice s' 12 13) 0));
  Spec.Lib.lemma_uint32s_from_le_inj 8 k k;
  Spec.Lib.lemma_uint32s_from_le_inj 3 n n;
  Seq.lemma_eq_intro s' (Spec.setup k n (H32.v c'))


private
val lemma_state_counter:
  k:Spec.key -> n:Spec.nonce -> c:Spec.counter ->
  Lemma (U32.v (Seq.index (Spec.setup k n (c)) 12) == c)
let lemma_state_counter k n c = ()


#reset-options "--max_fuel 0  --z3rlimit 400"

[@ "c_inline"]
private
val chacha20_core:
  log:log_t ->
  k:state ->
  st:state{disjoint st k} ->
  ctr:UInt32.t ->
  Stack log_t
    (requires (fun h -> live h k /\ live h st /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h0 st /\ live h0 k /\ invariant log h0 st
      /\ live h1 k /\ invariant updated_log h1 st /\ modifies_2 k st h0 h1
      /\ (let key = reveal_h32s (as_seq h1 k) in
          let stv = reveal_h32s (as_seq h1 st) in
          Seq.index stv 12 == ctr /\
         (match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             key == chacha20_core stv /\ k == k' /\ n == n'))))
[@ "c_inline"]
let chacha20_core log k st ctr =
  let h_0 = ST.get() in
  st.(12ul) <- uint32_to_sint32 ctr;
  lemma_invariant (reveal_h32s (as_seq h_0 st)) (Ghost.reveal log).k (Ghost.reveal log).n (get h_0 st 12) (uint32_to_sint32 ctr);
  copy_state k st;
  let h' = ST.get() in
  cut (as_seq h' k == as_seq h' st);
  rounds k;
  let h'' = ST.get() in
  cut (reveal_h32s (as_seq h'' k) == Spec.Chacha20.rounds (reveal_h32s (as_seq h' st)));
  sum_states k st;
  let h = ST.get() in
  cut (reveal_h32s (as_seq h k) == chacha20_core (reveal_h32s (as_seq h st)));
  Ghost.elift1 (fun l -> match l with | MkLog k n -> MkLog k n) log


[@ "c_inline"]
val chacha20_block:
  log:log_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  ctr:UInt32.t ->
  Stack log_t
    (requires (fun h -> live h stream_block /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ invariant log h0 st
      /\ invariant updated_log h1 st /\ modifies_2 stream_block st h0 h1
      /\ (let block = reveal_sbytes (as_seq h1 stream_block) in
         match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             block == chacha20_block k n (U32.v ctr) /\ k == k' /\ n == n')))
[@ "c_inline"]
let chacha20_block log stream_block st ctr =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  (**) let h_0 = ST.get() in
  let st' = Buffer.create (uint32_to_sint32 0ul) 16ul in
  (**) let h1 = ST.get() in
  let log' = chacha20_core log st' st ctr in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_2' st st' h0 h1 h2;
  uint32s_to_le_bytes stream_block st' 16ul;
  (**) let h = ST.get() in
  (**) lemma_modifies_2_1'' st stream_block h0 h2 h;
  (**) assert (reveal_sbytes (as_seq h stream_block) == chacha20_block (Ghost.reveal log').k (Ghost.reveal log').n (U32.v ctr));
  (**) assert (modifies_3_2 stream_block st h_0 h);
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 stream_block st hinit h0 h hfin;
  (**) Ghost.elift1 (fun l -> match l with | MkLog k n -> MkLog k n) log'


[@ "c_inline"]
val alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h))
[@ "c_inline"]
let alloc () =
  create (uint32_to_sint32 0ul) 16ul


[@ "c_inline"]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1
      /\ invariant log h1 st
      /\ (match Ghost.reveal log with MkLog k' n' -> k' == reveal_sbytes (as_seq h0 k)
           /\ n' == reveal_sbytes (as_seq h0 n))))
[@ "c_inline"]
let init st k n =
  setup st k n 0ul;
  let h = ST.get() in
  Ghost.elift2 (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 12 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n))) (Ghost.hide k) (Ghost.hide n)


#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len < 64 /\ U32.v len > 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (as_seq hi input))
     == Spec.CTR.xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (U32.v len)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_chacha20_counter_mode_1 ho output hi input len k n ctr =
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  Math.Lemmas.modulo_lemma (UInt32.v len) 64;
  assert(UInt32.v len / (Spec.CTR.(chacha20_ctx.blocklen * chacha20_ctx.incr)) = 0);
  let open Spec.CTR in
  assert((xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (UInt32.v len))) == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (UInt32.v len)));
  let ctx = chacha20_ctx in
  let len:nat = UInt32.v len in
  let counter = UInt32.v ctr in
  let blocks_len = (ctx.incr * ctx.blocklen) * (len / (ctx.blocklen * ctx.incr)) in
  let part_len   = len % (ctx.blocklen * ctx.incr) in
    (* TODO: move to a single lemma for clarify *)
    Math.Lemmas.lemma_div_mod len (ctx.blocklen * ctx.incr);
    Math.Lemmas.multiple_modulo_lemma (len / (ctx.blocklen * ctx.incr)) (ctx.blocklen * ctx.incr);
    Math.Lemmas.lemma_div_le (blocks_len) len ctx.blocklen;
    (* End TODO *)
  let blocks, last_block = Seq.split (as_seq hi input) blocks_len in
  let cipher_blocks = counter_mode_blocks ctx chacha20_cipher k n counter (reveal_sbytes blocks) in
  Seq.lemma_eq_intro cipher_blocks Seq.createEmpty;
  assert(ctx.incr * (Seq.length (as_seq hi input) / ctx.blocklen) = 0);
  Seq.lemma_eq_intro (Seq.append Seq.createEmpty (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 len))) (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 len));
  Seq.lemma_eq_intro (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (as_seq hi input)))
                     (Spec.CTR.xor #(len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (len)))


#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len >= 64
    /\ UInt32.v len % 64 = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes (as_seq hi input))
    == (let prefix, block = Seq.split (as_seq hi input) (UInt32.v len - 64) in    
      Math.Lemmas.lemma_mod_plus (Seq.length prefix) 1 (64);
      Math.Lemmas.lemma_div_le (Seq.length prefix) (UInt32.v len) 64;
      Spec.CTR.Lemmas.lemma_div (UInt32.v len) (64);
    let cipher        = Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes prefix) in
    let mask          = chacha20_cipher k n (UInt32.v ctr + (UInt32.v len / 64 - 1) ) in
    let eb            = Spec.CTR.xor (reveal_sbytes block) mask in
    Seq.append cipher eb))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_2 ho output hi input len k n ctr = ()


#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes (as_seq hi input))
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_0 ho output hi input len k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty


#reset-options " --max_fuel 0 --z3rlimit 400"


val update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + 1 < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ updated_log == log
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (chacha20_cipher k n (U32.v ctr)))))
let update output plain log st ctr =
  let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let b  = create (uint32_to_sint32 0ul) 48ul in
  (**) let h2 = ST.get() in
  let k  = Buffer.sub b 0ul  16ul in
  let ib = Buffer.sub b 16ul 16ul in
  let ob = Buffer.sub b 32ul 16ul in
  let l  = chacha20_core log k st ctr in
  (**) let h3 = ST.get() in
  (**) modifies_subbuffer_2 h2 h3 k st b;
  uint32s_from_le_bytes ib plain 16ul;
  (**) let h  = ST.get() in
  (**) modifies_subbuffer_1 h3 h ib b;
  map2 ob ib k 16ul (fun x y -> H32.(x ^^ y));
  (**) let h4  = ST.get() in
  (**) modifies_subbuffer_1 h h4 ob b;
  (**) lemma_modifies_1_trans b h3 h h4;
  (**) lemma_modifies_2_1' b st h2 h3 h4;
  (**) lemma_modifies_0_2 st b h1 h2 h4;
  uint32s_to_le_bytes output ob 16ul;
  (**) let h5  = ST.get() in
  (**) lemma_modifies_2_1'' st output h1 h4 h5;
  Hacl.Impl.Xor.Lemmas.lemma_xor_uint32s_to_bytes (reveal_sbytes (as_seq h0 plain))
                                                       (reveal_h32s (as_seq h k));
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 st output h0 h1 h5 hfin;
  l

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len < 64 /\ UInt32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == (let mask = chacha20_cipher k n (UInt32.v ctr+(UInt32.v len / 64)) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask))))
let update_last output plain len log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h = ST.get() in
  let block = create (uint8_to_sint8 0uy) 64ul in
  (**) let h' = ST.get() in
  let l = chacha20_block log block st ctr in
  (**) let h'' = ST.get() in
  (**) lemma_modifies_0_2' st block h h' h'';
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (fun x y -> H8.(x ^^ y));
  (**) let h1 = ST.get() in
  (**) lemma_modifies_2_1'' st output h h'' h1;
  (**) lemma_chacha20_counter_mode_1 h1 output h0 plain len (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 st output h0 h h1 hfin;
  l


#reset-options " --max_fuel 0 --z3rlimit 100"

private
val lemma_aux_modifies_2: #a:Type -> #a':Type -> h:mem -> b:buffer a{live h b} -> b':buffer a'{live h b'} -> Lemma
  (requires (True))
  (ensures (modifies_2 b b' h h))
let lemma_aux_modifies_2 #a #a' h b b' =
  lemma_intro_modifies_2 b b' h h

private
val lemma_chacha20_counter_mode_def_0:
  s:Seq.seq Hacl.UInt8.t{Seq.length s = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes s)
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_def_0 s k n ctr =
  Seq.lemma_eq_intro s Seq.createEmpty


#reset-options "--max_fuel 0  --z3rlimit 200"

private
val chacha20_counter_mode_blocks:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:UInt32.t{64 * UInt32.v len = length output /\ length output = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1 /\ invariant log h1 st
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 200"
let chacha20_counter_mode_blocks output plain len log st ctr =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ invariant log h1 st /\ modifies_2 output st h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ (match Ghost.reveal log with | MkLog k n ->
      reveal_sbytes (Seq.slice (as_seq h1 output) 0 (64 * i))
      == Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (Seq.slice (as_seq h0 plain) 0 (64 * i))))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    let o'' = Buffer.sub output 0ul (64ul *^ i +^ 64ul) in
    let b'' = Buffer.sub plain  0ul (64ul *^ i +^ 64ul) in
    let b  = Buffer.sub plain (64ul *^ i) 64ul in
    let b' = Buffer.sub plain 0ul (64ul *^ i)  in
    let o  = Buffer.sub output (64ul *^ i) 64ul in
    let o' = Buffer.sub output 0ul (64ul *^ i)  in
    let log' = update o b log st FStar.UInt32.(ctr+^ i) in
    let h' = ST.get() in
    (**) modifies_subbuffer_2 h h' o st output;
    (**) lemma_modifies_2_trans output st h0 h h';
    no_upd_lemma_2 h h' o st b;
    no_upd_lemma_2 h h' o st b';
    no_upd_lemma_2 h h' o st o';
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (as_seq h' (Buffer.sub output 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (as_seq h0 (Buffer.sub plain 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h0 plain) 0 (64 * v i)) (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h' output) 0 (64 * v i)) (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64)));
    lemma_chacha20_counter_mode_2 h o'' h0 b'' (64ul *^ i +^ 64ul) (MkLog?.k (Ghost.reveal log)) (MkLog?.n (Ghost.reveal log)) ctr
  in
  let o0 = Buffer.sub output 0ul 0ul in
  let i0 = Buffer.sub plain  0ul 0ul in
  Seq.lemma_eq_intro (as_seq h0 o0) (Seq.slice (as_seq h0 output) 0 0);
  Seq.lemma_eq_intro (as_seq h0 i0) (Seq.slice (as_seq h0 plain) 0 0);
  lemma_aux_modifies_2 h0 output st;
  lemma_chacha20_counter_mode_def_0 (Seq.slice (as_seq h0 plain) 0 0) (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 0) Seq.createEmpty;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (64 * UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * UInt32.v len)) (as_seq h plain)


val chacha20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let chacha20_counter_mode output plain len log st ctr =
  assert_norm(pow2 6 = 64);
  let open FStar.UInt32 in
  let blocks_len = (len >>^ 6ul) in
  let part_len   = len &^ 0x3ful in
  UInt.logand_mask (UInt32.v len) 6;
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  (**) let h0 = ST.get() in
  let output' = Buffer.sub output 0ul (64ul *^ blocks_len) in
  let plain'  = Buffer.sub plain  0ul (64ul *^ blocks_len) in
  let output'' = Buffer.sub output (64ul *^ blocks_len) part_len in
  let plain''  = Buffer.sub plain  (64ul *^ blocks_len) part_len in
  chacha20_counter_mode_blocks output' plain' blocks_len log st ctr;
  (**) let h1 = ST.get() in
  (**) modifies_subbuffer_2 h0 h1 output' st output;
  if FStar.UInt32.(part_len >^ 0ul) then (
    let _ = update_last output'' plain'' part_len log st FStar.UInt32.(ctr +^ blocks_len) in
    (**) let h' = ST.get() in
    (**) modifies_subbuffer_2 h1 h' output'' st output)
  else 
    (**) lemma_modifies_sub_2 h1 h1 output st;
  let h = ST.get() in
  (**) lemma_modifies_2_trans output st h0 h1 h;
  Seq.lemma_eq_intro (Seq.append (as_seq h output') Seq.createEmpty) (as_seq h output');
  Seq.lemma_eq_intro (as_seq h output) (Seq.append (as_seq h output') (as_seq h output''));
  Seq.lemma_eq_intro (as_seq h0 plain) (Seq.append (as_seq h0 plain') (as_seq h0 plain''));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher (Ghost.reveal log).k (Ghost.reveal log).n (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain)));
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = U32.v ctr in
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n ctr plain)))
let chacha20 output plain len k n ctr =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let st = alloc () in
  (**) let h1 = ST.get() in
  let l  = init st k n in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' st h0 h1 h2;
  let l' = chacha20_counter_mode output plain len l st ctr in
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_2 output st h0 h2 h3;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 output hinit h0 h3 hfin
*)
