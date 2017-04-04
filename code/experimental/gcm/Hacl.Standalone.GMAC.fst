module Hacl.Standalone.GMAC

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H128 = Hacl.UInt128

open Spec.GF128

open Hacl.Spec.GMAC
open Hacl.Impl.GF128

open FStar.Mul
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer
open FStar.Endianness
open Hacl.Endianness
open Hacl.Spec.Endianness
open Hacl.Cast

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* GMAC state *)
noeq type gmac_state = {ram:buffer H128.t; len:buffer U32.t}

private let decode_pmsg (pmsg:H128.t) (len:U32.t{U32.v len <= 16}) : GTot word =
  slice (big_bytes 16ul (H128.v pmsg)) 0 (U32.v len)

let live_st h (st:gmac_state) : Type0 =
  live h st.ram /\ live h st.len /\ disjoint st.ram st.len

let valid_pmsg (pmsg:H128.t) (len:U32.t) : Type0 =
  U32.v len < 16 /\ pad (decode_pmsg pmsg len) = big_bytes 16ul (H128.v pmsg)

let valid_st h (st:gmac_state) : Type0 =
  live_st h st /\ length st.ram = 3 /\ length st.len = 1 /\
  valid_pmsg (get h st.ram 2) (get h st.len 0)
  

(* Get information from state *)

private let get_len h (st:gmac_state{valid_st h st}) : GTot U32.t = get h st.len 0

private let get_r h (st:gmac_state{valid_st h st}) : GTot elem = sel_elem h (sub st.ram 0ul 1ul)
private let get_acc h (st:gmac_state{valid_st h st}) : GTot elem = sel_elem h (sub st.ram 1ul 1ul)
private let get_pmsg h (st:gmac_state{valid_st h st}) :
  GTot (pmsg:bytes{Seq.length pmsg = U32.v (get h st.len 0)}) =
  decode_pmsg (get h st.ram 2) (get h st.len 0)

private val as_pure_st: h:HyperStack.mem -> st:gmac_state{valid_st h st} -> GTot (pst:gmac_state_)
let as_pure_st h st = MkState (get_r h st) (get_acc h st) (get_pmsg h st)


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* Useful lemmas *)

private let valid_pmsg_ (pmsg:H128.t) (len:U32.t) : Type0 =
  U32.v len < 16 /\ H128.v pmsg % (pow2 (8 * (16 - U32.v len))) = 0

private val zero_div_mod: n:pos -> Lemma (0 / n = 0 /\ 0 % n = 0)
let zero_div_mod n = Math.Lemmas.multiple_division_lemma 0 n; Math.Lemmas.multiple_modulo_lemma 0 n

private val lemma_is_valid_pmsg_: pmsg:H128.t -> len:U32.t{valid_pmsg_ pmsg len} -> i:nat{i < 16 - U32.v len} ->
  Lemma (requires True)
  (ensures (Seq.index (slice (big_bytes 16ul (H128.v pmsg)) (U32.v len) 16) i = 0uy))
  [SMTPat (Seq.index (slice (big_bytes 16ul (H128.v pmsg)) (U32.v len) 16) i)]
let lemma_is_valid_pmsg_ pmsg len i =
  lemma_index_big_bytes 16ul (H128.v pmsg) (U32.v len + i);
  Math.Lemmas.pow2_modulo_division_lemma_1 (H128.v pmsg) (8 * (16 - U32.v len - i - 1)) (8 * (16 - U32.v len - i));
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (H128.v pmsg) (8 * (16 - U32.v len - i)) (8 * (16 - U32.v len));
  zero_div_mod (pow2 (8 * (16 - U32.v len - i)));
  zero_div_mod (pow2 (8 * (16 - U32.v len - i - 1)))
  
private val lemma_is_valid_pmsg: pmsg:H128.t -> len:U32.t -> Lemma
  (requires (valid_pmsg_ pmsg len))
  (ensures (valid_pmsg pmsg len))
  [SMTPat (valid_pmsg pmsg len)]
let lemma_is_valid_pmsg pmsg len =
  lemma_eq_intro (Seq.create (16 - U32.v len) 0uy) (slice (big_bytes 16ul (H128.v pmsg)) (U32.v len) 16);
  lemma_eq_intro (pad (decode_pmsg pmsg len)) (big_bytes 16ul (H128.v pmsg))
  

(* Main functions *)

#reset-options "--z3rlimit 80 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val gmac_alloc: unit -> StackInline gmac_state
  (requires (fun _ -> True))
  (ensures (fun h0 st h1 -> ~(contains h0 st.ram) /\ ~(contains h0 st.len) /\
    frameOf st.ram == h0.tip /\ frameOf st.len == h0.tip /\
    modifies_0 h0 h1 /\ valid_st h1 st))
let gmac_alloc () =
  let h0 = ST.get() in
  let ram = create zero_128 3ul in
  let h1 = ST.get() in
  lemma_reveal_modifies_0 h0 h1;
  let len = create 0ul 1ul in
  {ram = ram; len = len}

val gmac_init: st:gmac_state -> r:keyB{disjoint st.ram r /\ disjoint st.len r} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h r))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ valid_st h1 st /\ live h1 r /\
    modifies_2 st.ram st.len h0 h1 /\
    as_pure_st h1 st = gmac_init_spec (as_seq h0 r)))
let gmac_init st r =
  let h0 = ST.get() in
  let rv = encodeB r in
  st.ram.(0ul) <- rv;
  st.ram.(1ul) <- zero_128;
  st.ram.(2ul) <- zero_128;
  st.len.(0ul) <- 0ul;
  let h1 = ST.get() in
  zero_div_mod (pow2 (8 * 16));
  Seq.lemma_eq_intro (get_r h1 st) (encode (reveal_sbytes (as_seq h0 r)));
  fzero_lemma zero_128;
  Seq.lemma_eq_intro (get_acc h1 st) zero;
  Seq.lemma_eq_intro (get_pmsg h1 st) (Seq.createEmpty)

private val update_pmsg: pmsg:H128.t -> len_1:U32.t{valid_pmsg_ pmsg len_1} ->
  nmsg:wordB -> len_2:U32.t{length nmsg = U32.v len_2 /\ U32.(v (len_1 +^ len_2)) <= 16} -> StackInline H128.t
  (requires (fun h -> live h nmsg))
  (ensures (fun h0 r h1 -> live h0 nmsg /\ modifies_0 h0 h1 /\ valid_pmsg_ r U32.(len_1 +^ len_2) /\
    decode_pmsg r U32.(len_1 +^ len_2) = decode_pmsg pmsg len_1 @| reveal_sbytes (as_seq h0 nmsg)))
let update_pmsg pmsg len_1 nmsg len_2 =
  let h0 = ST.get() in
  push_frame();
  let nmsg_16 = create (uint8_to_sint8 0uy) 16ul in
  blit nmsg 0ul nmsg_16 len_1 len_2;
  let h' = ST.get() in
  let pmsg_ = encodeB nmsg_16 in
  pop_frame();
  let h1 = ST.get() in
  lemma_eq_intro (slice ( (as_seq h' nmsg_16)) (U32.v len_1) (U32.v len_1 + U32.v len_2)) ( (as_seq h0 nmsg));
  admit()
  (*
  admit();
  lemma_eq_intro (sel_word h' nmsg_16) (pad (sel_word h' nmsg_16));
  FStar.UInt.to_vec_lemma_2 (big_endian (sel_word h' nmsg_16)) (H128.v pmsg_);
  assert(big_endian (sel_word h' nmsg_16) = H128.v pmsg_);
  lemma_eq_intro (Seq.create (U32.v len_1) 0uy) (slice (sel_word h' nmsg_16) 0 (U32.v len_1));
  admit();
  lemma_eq_intro (Seq.create (U32.v len_1) 0uy @| slice (sel_word h' nmsg_16) (U32.v len_1) 16)
    (sel_word h' nmsg_16);
  admit();
  *)
  assume(H128.v pmsg + H128.v pmsg_ < pow2 128);
  assume(valid_pmsg_ H128.(pmsg +^ pmsg_) U32.(len_1 +^ len_2));
  assume(slice (decode_pmsg H128.(pmsg +^ pmsg_) U32.(len_1 +^ len_2)) 0 (U32.v len_1) = decode_pmsg pmsg len_1);
  assume(slice (decode_pmsg H128.(pmsg +^ pmsg_) U32.(len_1 +^ len_2)) (U32.v len_1) (U32.v len_1 + U32.v len_2) = reveal_sbytes (as_seq h0 nmsg));
  lemma_eq_intro (decode_pmsg H128.(pmsg +^ pmsg_) U32.(len_1 +^ len_2)) (decode_pmsg pmsg len_1 @| reveal_sbytes (as_seq h0 nmsg));
  H128.(pmsg +^ pmsg_)
  

val gmac_update: st:gmac_state -> msg:buffer H8.t{disjoint st.ram msg /\ disjoint st.len msg} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h msg))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_2 st.ram st.len h0 h1 /\
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (sel_word h0 msg)))
let gmac_update st msg = admit()


(*
inline_for_extraction private
val gmac_set_r: st:gmac_state -> r:wordB_16{disjoint st.r_acc r /\ disjoint st.s_pmsg_len r} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h r))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ valid_st h1 st /\ live h1 r /\
    modifies_1 st.r_acc h0 h1 /\
    get_r h1 st = encode (as_seq h0 r) /\ get_s h1 st = get_s h0 st /\
    get_acc h1 st = get_acc h0 st /\ get_pmsg h1 st = get_pmsg h0 st))
let gmac_set_r st r =
  let h0 = ST.get() in
  let st_r = sub st.r_acc 0ul 1ul in
  let rv = load128_be r in
  st_r.(0ul) <- rv;
  let h1 = ST.get() in
  (* get_r h1 st = encode (as_seq h0 r) *)
  Seq.lemma_eq_intro (get_r h1 st) (encode (as_seq h0 r));
  (* get_acc h1 st = get_acc h0 st *)
  let st_acc = sub st.r_acc 1ul 1ul in
  assert(disjoint st_r st_acc);
  lemma_reveal_modifies_1 st_r h0 h1;
  (* get_s h1 st = get_s h0 st *)
  lemma_sub_spec st.s_pmsg_len 0ul 16ul h0;
  lemma_sub_spec st.s_pmsg_len 0ul 16ul h1;
  (* get_pmsg h1 st = get_pmsg h0 st *)
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h0 st.s_pmsg_len 32)) h0;
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h1 st.s_pmsg_len 32)) h1

inline_for_extraction private
val gmac_set_s: st:gmac_state -> s:tagB{disjoint st.r_acc s /\ disjoint st.s_pmsg_len s} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h s))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 s /\ valid_st h1 st /\ live h1 s /\
    modifies_1 st.s_pmsg_len h0 h1 /\
    get_r h1 st = get_r h0 st /\ get_s h1 st = as_seq h0 s /\
    get_acc h1 st = get_acc h0 st /\ get_pmsg h1 st = get_pmsg h0 st))
let gmac_set_s st s =
  let h0 = ST.get() in
  let st_s = sub st.s_pmsg_len 0ul 16ul in
  blit s 0ul st_s 0ul 16ul;
  let h1 = ST.get() in
  (* valid_st h1 st *)
  let st_len = sub st.s_pmsg_len 32ul 1ul in
  assert(disjoint st_s st_len);
  lemma_reveal_modifies_1 st_s h0 h1;
  lemma_sub_spec st.s_pmsg_len 32ul 1ul h0;
  lemma_sub_spec st.s_pmsg_len 32ul 1ul h1;
  Seq.lemma_index_slice (as_seq h0 st.s_pmsg_len) 32 33 0;
  Seq.lemma_index_slice (as_seq h1 st.s_pmsg_len) 32 33 0;
  (* get_s h1 st = as_seq h0 s *)
  Seq.lemma_eq_intro (Seq.slice (get_s h1 st) 0 16) (get_s h1 st);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 s) 0 16) (as_seq h0 s);
  Seq.lemma_eq_intro (get_s h1 st) (as_seq h0 s);
  (* get_pmsg h1 st = get_pmsg h0 st *)
  let st_pmsg = sub st.s_pmsg_len 16ul 16ul in
  assert(disjoint st_s st_pmsg);
  lemma_reveal_modifies_1 st_s h0 h1;
  (* get_r h1 st = get_r h0 st *)
  lemma_sub_spec st.r_acc 0ul 1ul h0;
  lemma_sub_spec st.r_acc 0ul 1ul h1;
  (* get_acc h1 st = get_acc h0 st *)
  lemma_sub_spec st.r_acc 1ul 1ul h0;
  lemma_sub_spec st.r_acc 1ul 1ul h1

inline_for_extraction private
val gmac_init_acc: st:gmac_state -> Stack unit
  (requires (fun h -> valid_st h st))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ valid_st h1 st /\
    modifies_1 st.r_acc h0 h1 /\
    get_r h1 st = get_r h0 st /\ get_s h1 st = get_s h0 st /\
    get_acc h1 st = zero /\ get_pmsg h1 st = get_pmsg h0 st))
let gmac_init_acc st =
  let h0 = ST.get() in
  let st_acc = sub st.r_acc 1ul 1ul in
  st_acc.(0ul) <- zero_128;
  let h1 = ST.get() in
  (* get_r h1 st = get_r h0 st *)
  let st_r = sub st.r_acc 0ul 1ul in
  assert(disjoint st_acc st_r);
  lemma_reveal_modifies_1 st_acc h0 h1;
  (* get_acc h1 st = zero *)
  fzero_lemma zero_128;
  Seq.lemma_eq_intro (get_acc h1 st) zero;
  (* get_s h1 st = get_s h0 st *)
  lemma_sub_spec st.s_pmsg_len 0ul 16ul h0;
  lemma_sub_spec st.s_pmsg_len 0ul 16ul h1;
  (* get_pmsg h1 st = get_pmsg h0 st *)
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h0 st.s_pmsg_len 32)) h0;
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h1 st.s_pmsg_len 32)) h1

inline_for_extraction private
val gmac_init_pmsg: st:gmac_state -> Stack unit
  (requires (fun h -> valid_st h st))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ valid_st h1 st /\
    modifies_1 st.s_pmsg_len h0 h1 /\
    get_r h1 st = get_r h0 st /\ get_s h1 st = get_s h0 st /\
    get_acc h1 st = get_acc h0 st /\ get_pmsg h1 st = Seq.createEmpty))
let gmac_init_pmsg st =
  let h0 = ST.get() in
  let st_len = sub st.s_pmsg_len 32ul 1ul in
  st_len.(0ul) <- uint8_to_sint8 0uy;
  let h1 = ST.get() in
  (* valid_st h1 st *)
  lemma_sub_spec st.s_pmsg_len 32ul 1ul h1;
  Seq.lemma_index_slice (as_seq h1 st.s_pmsg_len) 32 33 0;
  (* get_s h1 st = get_s h0 st *)
  let st_s = sub st.s_pmsg_len 0ul 16ul in
  assert(disjoint st_len st_s);
  lemma_reveal_modifies_1 st_len h0 h1;
  (* get_pmsg h1 st = Seq.createEmpty *)
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h1 st.s_pmsg_len 32)) h1;
  Seq.lemma_eq_intro (get_pmsg h1 st) (Seq.createEmpty);
  (* get_r h1 st = get_r h0 st *)
  lemma_sub_spec st.r_acc 0ul 1ul h0;
  lemma_sub_spec st.r_acc 0ul 1ul h1;
  (* get_acc h1 st = get_acc h0 st *)
  lemma_sub_spec st.r_acc 1ul 1ul h0;
  lemma_sub_spec st.r_acc 1ul 1ul h1


(* Main GMAC functions *)
val gmac_init: st:gmac_state -> r:wordB_16{disjoint st.r_acc r /\ disjoint st.s_pmsg_len r} ->
  s:tagB{disjoint st.r_acc s /\ disjoint st.s_pmsg_len s /\ disjoint r s} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h r /\ live h s))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ live h0 s /\
    valid_st h1 st /\ live h1 r /\ live h1 s /\ modifies_2 st.r_acc st.s_pmsg_len h0 h1 /\
    as_pure_st h1 st == gmac_init_spec (as_seq h0 r) (as_seq h0 s)))
let gmac_init st r s =
  gmac_set_r st r;
  gmac_set_s st s;
  gmac_init_acc st;
  gmac_init_pmsg st
*)
