module GCM

module U32 = FStar.UInt32
module H8  = Hacl.UInt8

open Spec.GF128

open Hacl.Impl.GF128
open Hacl.Spec.GMAC
open Hacl.Standalone.GMAC

open FStar.Mul
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer
open Hacl.Spec.Endianness

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val alloc: unit -> StackInline gmac_state
  (requires (fun _ -> True))
  (ensures (fun h0 st h1 -> ~(contains h0 st.r_acc) /\ ~(contains h0 st.pmsg) /\ ~(contains h0 st.len) /\
    frameOf st.r_acc == h0.tip /\ frameOf st.pmsg == h0.tip /\ frameOf st.len == h0.tip /\
    modifies_0 h0 h1 /\ valid_st h1 st))
let alloc () = gmac_alloc ()

val init: st:gmac_state ->
  r:keyB{disjoint st.r_acc r /\ disjoint st.pmsg r /\ disjoint st.len r} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h r))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 r /\ valid_st h1 st /\ live h1 r /\
    modifies_2 st.r_acc st.len h0 h1))
let init st r = gmac_init st r

val update_block: st:gmac_state ->
  msg:tagB{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ get_pmsg h st = createEmpty))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_1 st.r_acc h0 h1))
let update_block st msg = gmac_update_block st msg

val update: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  blen:U32.t{length msg = 16 * U32.v blen} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg /\ get_pmsg h st = createEmpty))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_1 st.r_acc h0 h1))
let rec update st msg blen =
  if U32.(blen =^ 0ul) then ()
  else begin
    let block = sub msg 0ul 16ul in
    let msg'  = offset msg 16ul in
    let blen'  = U32.(blen -^ 1ul) in
    update_block st block;
    update st msg' blen'
  end

val updateL: st:gmac_state ->
  msg:buffer H8.t{disjoint st.r_acc msg /\ disjoint st.pmsg msg /\ disjoint st.len msg} ->
  len:U32.t{length msg = U32.v len} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h msg))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 msg /\ valid_st h1 st /\ live h1 msg /\
    modifies_3 st.r_acc st.pmsg st.len h0 h1))
let updateL st msg len = gmac_update st msg len

val finish: st:gmac_state ->
  s:tagB{disjoint st.r_acc s /\ disjoint st.pmsg s /\ disjoint st.len s} ->
  tag:tagB{disjoint st.r_acc tag /\ disjoint st.pmsg tag /\ disjoint st.len tag /\ disjoint s tag} ->
  Stack unit
  (requires (fun h -> valid_st h st /\ live h s /\ live h tag))
  (ensures (fun h0 _ h1 -> valid_st h0 st /\ live h0 s /\ live h0 tag /\ valid_st h1 st /\ live h1 s /\ live h1 tag /\
    modifies_3 st.r_acc st.pmsg tag h0 h1))
let finish st s tag = gmac_finish st s tag


val crypto_onetimeauth:
  output:tagB ->
  input:buffer H8.t{disjoint input output} ->
  len:U32.t{length input = U32.v len} ->
  r:keyB{disjoint r output /\ disjoint r input} ->
  s:tagB{disjoint s output /\ disjoint s input /\ disjoint s r} ->
  Stack unit
  (requires (fun h -> live h output /\ live h input /\ live h r /\ live h s))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 r /\ live h0 s /\
    live h1 output /\ live h1 input /\ live h1 r /\ live h1 s /\
    modifies_1 output h0 h1 /\
    reveal_sbytes (as_seq h1 output) =
      mac (encode_bytes (reveal_sbytes (as_seq h0 input)))
          (encode (reveal_sbytes (as_seq h0 r)))
	  (reveal_sbytes (as_seq h0 s))))
let crypto_onetimeauth output input len r s =
  let h0 = ST.get() in
  lemma_gmac_spec (as_seq h0 input) (as_seq h0 r) (as_seq h0 s);
  gmac_onetimeauth output input len r s
