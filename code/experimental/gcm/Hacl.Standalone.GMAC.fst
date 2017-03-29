module Hacl.Standalone.GMAC

module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H128 = Hacl.UInt128
module Spec = Hacl.Spec.GMAC

open Spec
open Spec.GF128
open Hacl.Impl.GF128

open FStar.Mul
open FStar.Seq
open FStar.Buffer
open FStar.Endianness
open Hacl.Cast

(* GMAC state *)
noeq type gmac_state = {r_acc:buffer H128.t; s_pmsg_len:buffer H8.t}

let live_st h (st:gmac_state) : Type0 =
  live h st.r_acc /\ live h st.s_pmsg_len /\ disjoint st.r_acc st.s_pmsg_len

let valid_st h (st:gmac_state) : Type0 =
  live_st h st /\ length st.r_acc = 2 /\ length st.s_pmsg_len = 33 /\
  H8.v (get h st.s_pmsg_len 32) < 16


(* Get information from state *)
#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

private val h8_to_u32: x:H8.t -> GTot (u:U32.t{H8.v x = U32.v u})
let h8_to_u32 x = 
  let cast (x:nat{x < pow2 32 - 1}) : GTot (UInt.uint_t 32) = x in
  assert(H8.v x < pow2 32 - 1);
  U32.uint_to_t (cast (H8.v x))

private let get_r h (st:gmac_state{valid_st h st}) : GTot elem =
  sel_elem h (sub st.r_acc 0ul 1ul)
private let get_s h (st:gmac_state{valid_st h st}) : GTot tag =
  as_seq h (sub st.s_pmsg_len 0ul 16ul)
private let get_acc h (st:gmac_state{valid_st h st}) : GTot elem =
  sel_elem h (sub st.r_acc 1ul 1ul)
private let get_pmsg h (st:gmac_state{valid_st h st}) : GTot (pmsg:bytes{Seq.length pmsg < 16}) =
  as_seq h (sub st.s_pmsg_len 16ul (h8_to_u32 (get h st.s_pmsg_len 32)))

private val as_pure_st: h:HyperStack.mem -> st:gmac_state{valid_st h st} -> GTot (pst:gmac_state_)
let as_pure_st h st = MkState (get_r h st) (get_s h st) (get_acc h st) (get_pmsg h st)


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val gmac_init: st:gmac_state -> r:wordB_16{disjoint st.r_acc r /\ disjoint st.s_pmsg_len r} ->
  s:tagB{disjoint st.r_acc s /\ disjoint st.s_pmsg_len s /\ disjoint r s} -> Stack unit
  (requires (fun h -> valid_st h st /\ live h r /\ live h s))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ live h0 s /\
    valid_st h1 st /\ live h1 r /\ live h1 s /\ modifies_2 st.r_acc st.s_pmsg_len h0 h1 /\
    as_pure_st h1 st == gmac_init_spec (as_seq h0 r) (as_seq h0 s)))
let gmac_init st r s =
  let h0 = ST.get() in
  let st_r = sub st.r_acc 0ul 1ul in
  let rv = load128_be r in
  st_r.(0ul) <- rv;
  let st_s = sub st.s_pmsg_len 0ul 16ul in
  blit s 0ul st_s 0ul 16ul;
  let st_acc = sub st.r_acc 1ul 1ul in
  st_acc.(0ul) <- zero_128;
  let st_len = sub st.s_pmsg_len 32ul 1ul in
  st_len.(0ul) <- uint8_to_sint8 0uy;
  let h1 = ST.get() in
  (* valid_st h1 st *)
  lemma_sub_spec st.s_pmsg_len 32ul 1ul h1;
  Seq.lemma_index_slice (as_seq h1 st.s_pmsg_len) 32 33 0;
  (* get_r h1 st = encode (as_seq h0 r) *)
  Seq.lemma_eq_intro (get_r h1 st) (encode (as_seq h0 r));
  (* get_s h1 st = as_seq h0 s *)
  Seq.lemma_eq_intro (Seq.slice (get_s h1 st) 0 16) (get_s h1 st);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 s) 0 16) (as_seq h0 s);
  Seq.lemma_eq_intro (get_s h1 st) (as_seq h0 s);
  (* get_acc h1 st = zero *)
  fzero_lemma zero_128;
  Seq.lemma_eq_intro (get_acc h1 st) zero;
  lemma_sub_spec st.s_pmsg_len 16ul (h8_to_u32 (get h1 st.s_pmsg_len 32)) h1;
  Seq.lemma_eq_intro (get_pmsg h1 st) (Seq.createEmpty)


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
