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
noeq type gmac_state = {
  r_acc : (b:buffer H128.t{length b =  2});
  pmsg  : (b:buffer H8.t  {length b = 16});
  len   : (b:buffer U32.t {length b =  1})}

let live_st h (st:gmac_state) : Type0 =
  live h st.r_acc /\ live h st.pmsg /\ live h st.len /\
  disjoint st.r_acc st.pmsg /\ disjoint st.r_acc st.len /\ disjoint st.pmsg st.len

let valid_st h (st:gmac_state) : Type0 =
  live_st h st /\ U32.v (get h st.len 0) < 16

private let get_r h (st:gmac_state{live_st h st}) : GTot elem = sel_elem h (sub st.r_acc 0ul 1ul)
private let get_acc h (st:gmac_state{live_st h st}) : GTot elem = sel_elem h (sub st.r_acc 1ul 1ul)
private let get_pmsg h (st:gmac_state{valid_st h st}) : GTot bytes =
  reveal_sbytes (slice (as_seq h st.pmsg) 0 (U32.v (get h st.len 0)))

private val as_pure_st: h:HyperStack.mem -> st:gmac_state{valid_st h st} -> GTot (pst:gmac_state_)
let as_pure_st h st = MkState (get_r h st) (get_acc h st) (get_pmsg h st)


(* Assistant functions *)

#reset-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

private abstract val gmac_pmsg_concat: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ U32.v (get h st.len 0) + U32.v l <= 16))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ live_st h1 st /\ live h1 msg /\
    modifies_2 st.pmsg st.len h0 h1 /\
    get_r h0 st = get_r h1 st /\ get_acc h0 st = get_acc h1 st /\
    U32.v (get h1 st.len 0) = U32.v (get h0 st.len 0) + U32.v l /\
    U32.v (get h1 st.len 0) <= 16 /\
    reveal_sbytes (slice (as_seq h1 st.pmsg) 0 (U32.v (get h1 st.len 0))) = get_pmsg h0 st @| reveal_sbytes (as_seq h0 msg)))
let gmac_pmsg_concat st msg l =
  let h0 = ST.get() in
  let pl = st.len.(0ul) in
  blit msg 0ul st.pmsg pl l;
  st.len.(0ul) <- U32.(pl +^ l);
  let h1 = ST.get() in
  assert(disjoint st.pmsg (sub st.r_acc 0ul 1ul));
  assert(disjoint st.pmsg (sub st.r_acc 1ul 1ul));
  let pmsg_1 = reveal_sbytes (slice (as_seq h1 st.pmsg) 0 (U32.v (get h1 st.len 0))) in
  lemma_eq_intro (slice (as_seq h1 st.pmsg) 0 (U32.v pl)) (slice (as_seq h0 st.pmsg) 0 (U32.v pl));
  lemma_eq_intro (slice pmsg_1 0 (U32.v pl)) (get_pmsg h0 st);
  lemma_eq_intro (slice (reveal_sbytes (as_seq h1 st.pmsg)) (U32.v pl) (U32.v pl + U32.v l)) (reveal_sbytes (slice (as_seq h1 st.pmsg) (U32.v pl) (U32.v pl + U32.v l)));
  lemma_eq_intro (slice (as_seq h1 st.pmsg) (U32.v pl) (U32.v pl + U32.v l)) (as_seq h0 msg);
  lemma_eq_intro pmsg_1 (get_pmsg h0 st @| reveal_sbytes (as_seq h0 msg))

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

private abstract val gmac_pmsg_padding: st:gmac_state ->
  Stack unit
  (requires (fun h -> valid_st h st /\ U32.v (get h st.len 0) > 0))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live_st h1 st /\
    modifies_1 st.pmsg h0 h1 /\
    get_r h0 st = get_r h1 st /\ get_acc h0 st = get_acc h1 st /\
    reveal_sbytes (as_seq h1 st.pmsg) = get_pmsg h0 st @| Seq.create (16 - U32.v (get h0 st.len 0)) 0uy))
let gmac_pmsg_padding st =
  let h0 = ST.get() in
  let pl = st.len.(0ul) in
  let pmsg = sub st.pmsg 0ul pl in
  let rest = sub st.pmsg pl U32.(16ul -^ pl) in
  fill rest (uint8_to_sint8 0uy) U32.(16ul -^ pl);
  let h' = ST.get() in
  assert(disjoint pmsg rest);
  lemma_reveal_modifies_1 rest h0 h';
  let h1 = ST.get() in
  lemma_eq_intro (reveal_sbytes (as_seq h1 st.pmsg)) (reveal_sbytes (slice (as_seq h1 st.pmsg) 0 (U32.v pl)) @| reveal_sbytes (slice (as_seq h1 st.pmsg) (U32.v pl) 16));
  lemma_eq_intro (reveal_sbytes (slice (as_seq h1 st.pmsg) 0 (U32.v pl))) (get_pmsg h0 st);
  lemma_eq_intro (slice (as_seq h1 st.pmsg) (U32.v pl) 16) (slice (as_seq h1 rest) 0 (16 - U32.v pl));
  lemma_eq_intro (slice (as_seq h1 rest) 0 (16 - U32.v pl)) (Seq.create (16 - U32.v pl) (uint8_to_sint8 0uy));
  lemma_eq_intro (reveal_sbytes (Seq.create (16 - U32.v pl) (uint8_to_sint8 0uy))) (Seq.create (16 - U32.v (get h0 st.len 0)) 0uy)

#reset-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
  
private abstract val gmac_update_short: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ U32.v (get h st.len 0) + U32.v l < 16))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_2 st.pmsg st.len h0 h1 /\ 
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
let gmac_update_short st msg l =
  let h0 = ST.get() in
  if U32.v l = 0 then lemma_eq_intro (get_pmsg h0 st) (get_pmsg h0 st @| reveal_sbytes (as_seq h0 msg))
  else gmac_pmsg_concat st msg l

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* NOTE: The spec is very lax. Make sure the pmsg is full before calling and set st.len as 0ul right after. *)
private abstract val gmac_full_pmsg_absorb: st:gmac_state -> Stack unit
  (requires (fun h -> live_st h st))
  (ensures (fun h0 _ h1 -> live_st h0 st /\ live_st h1 st /\
    modifies_1 st.r_acc h0 h1 /\ get_r h0 st = get_r h1 st /\
    get_acc h1 st = (get_acc h0 st +@ encode (reveal_sbytes (as_seq h0 st.pmsg))) *@ get_r h0 st))
let gmac_full_pmsg_absorb st =
  let h0 = ST.get() in
  let r = sub st.r_acc 0ul 1ul in
  let acc = sub st.r_acc 1ul 1ul in
  let bv = encodeB st.pmsg in
  acc.(0ul) <- H128.(acc.(0ul) ^^ bv);
  gf128_mul acc r;
  let h1 = ST.get() in
  assert(disjoint acc r);
  assert(disjoint acc st.len);
  lemma_reveal_modifies_1 acc h0 h1

private abstract val gmac_update_short_3: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ U32.v (get h st.len 0) + U32.v l < 16))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_3 st.r_acc st.pmsg st.len h0 h1 /\ 
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
let gmac_update_short_3 st msg l =
  let h0 = ST.get() in
  gmac_update_short st msg l;
  let h1 = ST.get() in
  lemma_reveal_modifies_2 st.pmsg st.len h0 h1;
  lemma_intro_modifies_3 st.r_acc st.pmsg st.len h0 h1

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

private abstract val gmac_update_exact_block: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ U32.v (get h st.len 0) + U32.v l = 16))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_3 st.r_acc st.pmsg st.len h0 h1 /\ 
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
let gmac_update_exact_block st msg l =
  let h0 = ST.get() in
  lemma_gmac_update_exact_block (as_pure_st h0 st) (as_seq h0 msg);
  gmac_pmsg_concat st msg l;
  let h' = ST.get() in
  lemma_eq_intro (as_seq h' st.pmsg) (slice (as_seq h' st.pmsg) 0 (U32.v (get h' st.len 0)));
  lemma_sub_spec st.r_acc 0ul 1ul h0;
  lemma_sub_spec st.r_acc 0ul 1ul h';
  lemma_sub_spec st.r_acc 1ul 1ul h0;
  lemma_sub_spec st.r_acc 1ul 1ul h';
  lemma_reveal_modifies_2 st.pmsg st.len h0 h';
  gmac_full_pmsg_absorb st;
  st.len.(0ul) <- 0ul;
  let h1 = ST.get() in
  lemma_eq_intro (get_pmsg h1 st) createEmpty;
  lemma_reveal_modifies_2 st.r_acc st.len h' h1;
  lemma_intro_modifies_3 st.r_acc st.pmsg st.len h0 h1

#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

abstract val gmac_update_0: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ get_pmsg h st = createEmpty))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_3 st.r_acc st.pmsg st.len h0 h1 /\ 
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
  (decreases (length msg))
let rec gmac_update_0 st msg l =
  let h0 = ST.get() in
  if U32.v l < 16 then gmac_update_short_3 st msg l
  else begin
    let block = sub msg 0ul 16ul in
    lemma_eq_intro (reveal_sbytes (as_seq h0 block)) (get_pmsg h0 st @| reveal_sbytes (slice (as_seq h0 msg) 0 16));
    let nmsg = sub msg 16ul U32.(l -^ 16ul) in
    let r = sub st.r_acc 0ul 1ul in
    let acc = sub st.r_acc 1ul 1ul in
    let bv = encodeB block in
    acc.(0ul) <- H128.(acc.(0ul) ^^ bv);
    gf128_mul acc r;
    let h' = ST.get() in
    lemma_reveal_modifies_1 acc h0 h';
    lemma_intro_modifies_3 st.r_acc st.pmsg st.len h0 h';
    gmac_update_0 st nmsg U32.(l -^ 16ul);
    let h1 = ST.get() in
    lemma_modifies_3_trans st.r_acc st.pmsg st.len h0 h' h1
  end

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

private abstract val gmac_last_nonempty: st:gmac_state -> Stack unit
  (requires (fun h -> valid_st h st /\ U32.v (get h st.len 0) > 0))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ valid_st h1 st /\
    modifies_2 st.r_acc st.pmsg h0 h1 /\
    get_acc h1 st = (get_acc h0 st +@ encode (get_pmsg h0 st)) *@ get_r h0 st))
let gmac_last_nonempty st =
  let h0 = ST.get() in
  gmac_pmsg_padding st;
  let h' = ST.get() in
  gmac_full_pmsg_absorb st;
  let h1 = ST.get() in
  lemma_eq_intro (pad (get_pmsg h0 st)) (pad (get_pmsg h0 st @| Seq.create (16 - U32.v (get h0 st.len 0)) 0uy))

#reset-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

private abstract val gmac_last_: st:gmac_state -> Stack unit
  (requires (fun h -> valid_st h st))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ valid_st h1 st /\
    modifies_2 st.r_acc st.pmsg h0 h1 /\
    get_acc h1 st = gmac_last_spec (as_pure_st h0 st)))
let gmac_last_ st =
  let pl = st.len.(0ul) in
  if U32.v pl = 0 then () else gmac_last_nonempty st


(* Main functions *)

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

abstract val gmac_alloc: unit -> StackInline gmac_state
  (requires (fun _ -> True))
  (ensures (fun h0 st h1 -> ~(contains h0 st.r_acc) /\ ~(contains h0 st.pmsg) /\ ~(contains h0 st.len) /\
    frameOf st.r_acc == h0.tip /\ frameOf st.pmsg == h0.tip /\ frameOf st.len == h0.tip /\
    modifies_0 h0 h1 /\ valid_st h1 st /\
    as_pure_st h1 st = gmac_alloc_spec))
let gmac_alloc () =
  let h0 = ST.get() in
  let r_acc = create zero_128 2ul in
  fzero_lemma zero_128;
  let h1 = ST.get() in
  lemma_reveal_modifies_0 h0 h1;
  let pmsg = create (uint8_to_sint8 0uy) 16ul in
  let h2 = ST.get() in
  lemma_reveal_modifies_0 h1 h2;
  let len = create 0ul 1ul in
  let h3 = ST.get() in
  let st = {r_acc = r_acc; pmsg = pmsg; len = len} in
  lemma_eq_intro (get_pmsg h3 st) createEmpty;
  st

abstract val gmac_init: st:gmac_state ->
  r:keyB{disjoint st.r_acc r /\ disjoint st.pmsg r /\ disjoint st.len r} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h r))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ valid_st h1 st /\ live h1 r /\
    modifies_2 st.r_acc st.len h0 h1 /\
    as_pure_st h1 st = gmac_init_spec (as_seq h0 r)))
let gmac_init st r =
  let h0 = ST.get() in
  let rv = encodeB r in
  st.r_acc.(0ul) <- rv;
  st.r_acc.(1ul) <- zero_128;
  st.len.(0ul) <- 0ul;
  let h1 = ST.get() in
  lemma_eq_intro (get_r h1 st) (encode (reveal_sbytes (as_seq h0 r)));
  fzero_lemma zero_128;
  lemma_eq_intro (get_acc h1 st) zero;
  lemma_eq_intro (get_pmsg h1 st) createEmpty

abstract val gmac_update: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  l:U32.t{length msg = U32.v l} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_3 st.r_acc st.pmsg st.len h0 h1 /\
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
let gmac_update st msg l =
  let h0 = ST.get() in
  let pl = st.len.(0ul) in
  if U32.v pl + U32.v l < 16 then gmac_update_short_3 st msg l
  else begin
    let msg_1 = sub msg 0ul U32.(16ul -^ pl) in
    let msg_2 = sub msg U32.(16ul -^ pl) U32.(l -^ (16ul -^ pl)) in
    gmac_update_exact_block st msg_1 U32.(16ul -^ pl);
    let h' = ST.get() in
    lemma_reveal_modifies_3 st.r_acc st.pmsg st.len h0 h';
    lemma_sub_spec msg U32.(16ul -^ pl) U32.(l -^ (16ul -^ pl)) h0;
    lemma_sub_spec msg U32.(16ul -^ pl) U32.(l -^ (16ul -^ pl)) h';
    lemma_eq_intro (get_pmsg h' st) createEmpty;
    gmac_update_0 st msg_2 U32.(l -^ (16ul -^ pl));
    let h1 = ST.get() in
    lemma_gmac_update_ (as_pure_st h0 st) (as_seq h0 msg_1) (as_seq h' msg_2);
    lemma_eq_intro (as_seq h0 msg) (as_seq h0 msg_1 @| as_seq h0 msg_2);
    lemma_modifies_3_trans st.r_acc st.pmsg st.len h0 h' h1
  end

abstract val gmac_update_block: st:gmac_state ->
  msg:tagB{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ get_pmsg h st = createEmpty))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_1 st.r_acc h0 h1 /\
    as_pure_st h1 st = gmac_update_spec (as_pure_st h0 st) (as_seq h0 msg)))
let gmac_update_block st msg =
  let h0 = ST.get() in
  lemma_eq_intro (get_pmsg h0 st @| reveal_sbytes (as_seq h0 msg)) (reveal_sbytes (as_seq h0 msg));
  let r = sub st.r_acc 0ul 1ul in
  let acc = sub st.r_acc 1ul 1ul in
  let bv = encodeB msg in
  acc.(0ul) <- H128.(acc.(0ul) ^^ bv);
  gf128_mul acc r;
  let h1 = ST.get() in
  assert(disjoint acc r);
  lemma_reveal_modifies_1 acc h0 h1;
  lemma_gmac_update_exact_block (as_pure_st h0 st) (as_seq h0 msg)

abstract val gmac_finish: st:gmac_state ->
  s:tagB{disjoint st.r_acc s /\ disjoint st.pmsg s /\ disjoint st.len s} ->
  tag:tagB{disjoint st.r_acc tag /\ disjoint st.pmsg tag /\ disjoint st.len tag /\ disjoint s tag} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h s /\ live h tag))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 s /\ live h0 tag /\ valid_st h1 st /\ live h1 s /\ live h1 tag /\
    modifies_3 st.r_acc st.pmsg tag h0 h1 /\
    reveal_sbytes (as_seq h1 tag) = gmac_finish_spec (as_pure_st h0 st) (as_seq h0 s)))
let gmac_finish st s tag =
  let h0 = ST.get() in
  let acc = sub st.r_acc 1ul 1ul in
  gmac_last_ st;
  let sv = encodeB s in
  let h' = ST.get() in
  lemma_reveal_modifies_2 st.r_acc st.pmsg h0 h';
  decodeB tag H128.(acc.(0ul) ^^ sv);
  let h1 = ST.get() in
  lemma_reveal_modifies_1 tag h' h1;
  lemma_intro_modifies_3 st.r_acc st.pmsg tag h0 h1

abstract val gmac_onetimeauth: tag:tagB ->
  msg:buffer H8.t{disjoint tag msg} ->
  len:U32.t{U32.v len = length msg} ->
  r:keyB{disjoint tag r /\ disjoint msg r} ->
  s:tagB{disjoint tag s /\ disjoint msg s /\ disjoint r s} ->
  Stack unit
  (requires (fun h -> live h tag /\ live h msg /\ live h r /\ live h s))
  (ensures (fun h0 _ h1 -> live h0 tag /\ live h0 msg /\ live h0 r /\ live h0 s /\
    live h1 tag /\ live h1 msg /\ live h1 r /\ live h1 s /\
    modifies_1 tag h0 h1 /\
    reveal_sbytes (as_seq h1 tag) = gmac_spec (as_seq h0 msg) (as_seq h0 r) (as_seq h0 s)))
let gmac_onetimeauth tag msg len r s =
  let h0 = ST.get() in
  push_frame();
  let h' = ST.get() in
  let st = gmac_alloc() in
  let h0' = ST.get() in
  lemma_reveal_modifies_0 h' h0';
  gmac_init st r;
  let h1' = ST.get() in
  lemma_reveal_modifies_2 st.r_acc st.len h0' h1';
  gmac_update st msg len;
  let h2' = ST.get() in
  lemma_reveal_modifies_3 st.r_acc st.pmsg st.len h1' h2';
  gmac_finish st s tag;
  let h3' = ST.get() in
  lemma_reveal_modifies_3 st.r_acc st.pmsg tag h2' h3';
  pop_frame();
  let h1 = ST.get() in
  lemma_intro_modifies_1 tag h0 h1
