module Hacl.Spec.GMAC

module Spec = Spec.GF128

open Spec

open FStar.Seq
open FStar.Endianness
open Hacl.Cast
open Hacl.Spec.Endianness

#set-options "--z3rlimit 30 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* Hacl types *)

type sbytes = seq Hacl.UInt8.t
type sword = w:sbytes{length w <= 16}
type sword_16 = w:sbytes{length w = 16}
type skey = sword_16
type stag = sword_16

let intro_sbytes (s:bytes) : GTot (s:sbytes) = seq_map uint8_to_sint8 s

(* Pure GMAC state and function specs *)

type gmac_state_ = | MkState: r:elem -> acc:elem -> pmsg:bytes{length pmsg < 16} -> gmac_state_

let gmac_alloc_spec : gmac_state_ = MkState zero zero createEmpty

val gmac_init_spec: r:skey -> GTot gmac_state_
let gmac_init_spec r = MkState (encode (reveal_sbytes r)) zero createEmpty

val gmac_update_spec: st:gmac_state_ -> msg:sbytes ->
  GTot (nst:gmac_state_{nst.r = st.r /\ length nst.pmsg = (length st.pmsg + length msg) % 16})
  (decreases (length msg))
let rec gmac_update_spec st msg =
  if length msg + length st.pmsg >= 16 then begin
    let block : word = st.pmsg @| reveal_sbytes (slice msg 0 (16 - length st.pmsg)) in
    let nmsg : sbytes = slice msg (16 - length st.pmsg) (length msg) in
    let nacc = (st.acc +@ (encode block)) *@ st.r in
    let nst = MkState st.r nacc createEmpty in
    gmac_update_spec nst nmsg
  end else begin
    MkState st.r st.acc (st.pmsg @| reveal_sbytes msg)
  end

val gmac_last_spec: st:gmac_state_ -> GTot elem
let gmac_last_spec st =
  if length st.pmsg = 0 then st.acc
  else (st.acc +@ (encode st.pmsg)) *@ st.r
    
val gmac_finish_spec: st:gmac_state_ -> s:stag ->
  GTot (t:tag{t = finish (gmac_last_spec st) (reveal_sbytes s)})
let gmac_finish_spec st s = 
  decode ((gmac_last_spec st) +@ (encode (reveal_sbytes s)))

val gmac_spec: msg:sbytes -> r:skey -> s:stag -> GTot tag
let gmac_spec msg r s =
  let st_0 = gmac_init_spec r in
  let st = gmac_update_spec st_0 msg in
  gmac_finish_spec st s
  
val flatten_sbytes: msgs:seq sbytes -> Tot sbytes (decreases (length msgs))
let rec flatten_sbytes msgs =
  if length msgs = 0 then createEmpty
  else (head msgs) @| (flatten_sbytes (tail msgs))
  
val gmac_update_spec_repeat: st:gmac_state_ -> msgs:seq sbytes -> GTot gmac_state_ (decreases (length msgs))
let rec gmac_update_spec_repeat st msgs =
  if length msgs = 0 then st
  else
    let nst = gmac_update_spec st (head msgs) in
    gmac_update_spec_repeat nst (tail msgs)


(* Useful lemmas *)

#reset-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

val lemma_encode_bytes_0: msg_1:bytes{length msg_1 = 0} -> msg_2:bytes{length msg_2 > 0 /\ length msg_2 <= 16} -> Lemma
  (requires True)
  (ensures (encode_bytes (msg_1 @| msg_2) = cons msg_2 (encode_bytes msg_1)))
  (decreases (length msg_1))
let lemma_encode_bytes_0 msg_1 msg_2 =
  lemma_eq_intro msg_1 createEmpty;
  lemma_eq_intro (msg_1 @| msg_2) msg_2;
  let l0 = FStar.Math.Lib.min (length msg_1 + length msg_2) 16 in
  let hd, tl = split (msg_1 @| msg_2) l0 in
  lemma_eq_intro hd msg_2;
  lemma_eq_intro tl createEmpty;
  lemma_eq_intro (encode_bytes tl) createEmpty;
  lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (snoc createEmpty msg_2);
  lemma_eq_intro (encode_bytes msg_1) createEmpty;
  lemma_eq_intro (snoc createEmpty msg_2) (cons msg_2 (encode_bytes msg_1))

val lemma_encode_bytes_16: msg_1:bytes{length msg_1 = 16} -> msg_2:bytes{length msg_2 > 0 /\ length msg_2 <= 16} -> Lemma
  (requires True)
  (ensures (encode_bytes (msg_1 @| msg_2) = cons msg_2 (encode_bytes msg_1)))
  (decreases (length msg_1))
let lemma_encode_bytes_16 msg_1 msg_2 =
  let l0 = FStar.Math.Lib.min (length msg_1 + length msg_2) 16 in
  let hd, tl = split (msg_1 @| msg_2) l0 in
  lemma_eq_intro hd msg_1;
  lemma_eq_intro tl msg_2;
  lemma_eq_intro (createEmpty @| msg_2) msg_2;
  lemma_encode_bytes_0 createEmpty msg_2;
  lemma_eq_intro (encode_bytes tl) (cons msg_2 createEmpty);
  lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (snoc (cons msg_2 createEmpty) msg_1);
  lemma_eq_intro (createEmpty @| msg_1) msg_1;
  lemma_encode_bytes_0 createEmpty msg_1;
  lemma_eq_intro (encode_bytes msg_1) (cons msg_1 createEmpty);
  lemma_eq_intro (cons msg_2 (encode_bytes msg_1)) (cons msg_2 (cons msg_1 createEmpty));
  lemma_eq_intro (snoc (cons msg_2 createEmpty) msg_1) (cons msg_2 (cons msg_1 createEmpty));
  lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (cons msg_2 (encode_bytes msg_1))
  
val lemma_encode_bytes: msg_1:bytes{length msg_1 % 16 = 0} -> msg_2:bytes{length msg_2 > 0 /\ length msg_2 <= 16} -> Lemma
  (requires True)
  (ensures (encode_bytes (msg_1 @| msg_2) = cons msg_2 (encode_bytes msg_1)))
  (decreases (length msg_1))
let rec lemma_encode_bytes msg_1 msg_2 =
  if length msg_1 = 0 then lemma_encode_bytes_0 msg_1 msg_2
  else if length msg_1 = 16 then lemma_encode_bytes_16 msg_1 msg_2
  else begin
    let l0 = FStar.Math.Lib.min (length msg_1 + length msg_2) 16 in
    let hd, tl = split (msg_1 @| msg_2) l0 in
    let hd_1, tl_1 = split msg_1 l0 in
    lemma_eq_intro hd hd_1;
    lemma_eq_intro tl (tl_1 @| msg_2);
    lemma_encode_bytes tl_1 msg_2;
    lemma_eq_intro (encode_bytes tl) (cons msg_2 (encode_bytes tl_1));
    lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (snoc (encode_bytes tl) hd);
    lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (snoc (cons msg_2 (encode_bytes tl_1)) hd);
    lemma_eq_intro (encode_bytes msg_1) (snoc (encode_bytes tl_1) hd_1);
    lemma_eq_intro (cons msg_2 (snoc (encode_bytes tl_1) hd_1)) (snoc (cons msg_2 (encode_bytes tl_1)) hd);
    lemma_eq_intro (encode_bytes (msg_1 @| msg_2)) (cons msg_2 (encode_bytes msg_1))
  end

val lemma_gmac_update_pmsg: st:gmac_state_ -> msg:sbytes -> Lemma
  (requires True)
  (ensures (let st' = MkState st.r st.acc createEmpty in
    gmac_update_spec st msg = gmac_update_spec st' (intro_sbytes st.pmsg @| msg)))
let lemma_gmac_update_pmsg st msg =
  let st' = MkState st.r st.acc createEmpty in
  if length st.pmsg + length msg >= 16 then begin
    let block : word = st.pmsg @| reveal_sbytes (slice msg 0 (16 - length st.pmsg)) in
    let block' : word = createEmpty @| reveal_sbytes (slice (intro_sbytes st.pmsg @| msg) 0 16) in
    lemma_eq_intro block block';
    let nmsg : sbytes = slice msg (16 - length st.pmsg) (length msg) in
    let nmsg' : sbytes = slice (intro_sbytes st.pmsg @| msg) 16 (length st.pmsg + length msg) in
    lemma_eq_intro nmsg nmsg'
  end else begin
    lemma_eq_intro (createEmpty @| reveal_sbytes (intro_sbytes st.pmsg @| msg)) (st.pmsg @| reveal_sbytes msg)
  end

val lemma_gmac_update_0: st:gmac_state_{length st.pmsg = 0} -> msg_1:sbytes -> msg_2:sbytes -> Lemma
  (requires True)
  (ensures (gmac_update_spec (gmac_update_spec st msg_1) msg_2 = gmac_update_spec st (msg_1 @| msg_2)))
  (decreases (length msg_1))
let rec lemma_gmac_update_0 st msg_1 msg_2 =
  lemma_eq_intro st.pmsg createEmpty;
  if length msg_1 >= 16 then begin
    let block : word = st.pmsg @| reveal_sbytes (slice msg_1 0 16) in
    let block' : word = st.pmsg @| reveal_sbytes (slice (msg_1 @| msg_2) 0 16) in
    lemma_eq_intro block block';
    let nmsg_1 : sbytes = slice msg_1 16 (length msg_1) in
    let nmsg' : sbytes = slice (msg_1 @| msg_2) 16 (length msg_1 + length msg_2) in
    lemma_eq_intro (nmsg_1 @| msg_2) nmsg';
    let nacc = (st.acc +@ (encode block)) *@ st.r in
    let nst = MkState st.r nacc createEmpty in
    lemma_gmac_update_0 nst nmsg_1 msg_2
  end else begin 
    let st' = MkState st.r st.acc (reveal_sbytes msg_1) in
    lemma_eq_intro (st.pmsg @| reveal_sbytes msg_1) (reveal_sbytes msg_1);
    lemma_eq_intro (intro_sbytes (reveal_sbytes msg_1)) msg_1;
    lemma_gmac_update_pmsg st' msg_2
  end

val lemma_gmac_update_: st:gmac_state_ -> msg_1:sbytes -> msg_2:sbytes -> Lemma
  (requires True)
  (ensures (gmac_update_spec (gmac_update_spec st msg_1) msg_2 = gmac_update_spec st (msg_1 @| msg_2)))
let lemma_gmac_update_ st msg_1 msg_2 =
  let st' = MkState st.r st.acc createEmpty in
  lemma_gmac_update_pmsg st msg_1;
  lemma_gmac_update_pmsg st (msg_1 @| msg_2);
  lemma_gmac_update_0 st' (intro_sbytes st.pmsg @| msg_1) msg_2;
  append_assoc (intro_sbytes st.pmsg) msg_1 msg_2

val lemma_gmac_update_empty: st:gmac_state_ -> Lemma (gmac_update_spec st createEmpty = st)
let lemma_gmac_update_empty st = lemma_eq_intro (st.pmsg @| createEmpty) st.pmsg

val lemma_gmac_update_exact_block: st:gmac_state_ -> msg:sbytes{length msg + length st.pmsg = 16} -> Lemma
  (gmac_update_spec st msg = MkState st.r ((st.acc +@ (encode (st.pmsg @| reveal_sbytes msg))) *@ st.r) createEmpty)
let lemma_gmac_update_exact_block st msg =
  let block : word = st.pmsg @| reveal_sbytes (slice msg 0 (16 - length st.pmsg)) in
  lemma_eq_intro block (st.pmsg @| reveal_sbytes msg);
  let nmsg : sbytes = slice msg (16 - length st.pmsg) (length msg) in
  lemma_eq_intro nmsg createEmpty;
  let nacc = (st.acc +@ (encode block)) *@ st.r in
  let nst = MkState st.r nacc createEmpty in
  lemma_gmac_update_empty nst

val lemma_gmac_update_last: st:gmac_state_{length st.pmsg = 0} ->
  msg:sbytes{length msg > 0 /\ length msg <= 16} -> Lemma
  (gmac_last_spec (gmac_update_spec st msg) = (st.acc +@ (encode (reveal_sbytes msg))) *@ st.r)
let lemma_gmac_update_last st msg = 
  let st' = gmac_update_spec st msg in
  lemma_eq_intro st.pmsg createEmpty;
  if length msg = 16 then begin
    let block : word = st.pmsg @| reveal_sbytes (slice msg 0 16) in
    lemma_eq_intro block (reveal_sbytes msg);
    let nmsg : sbytes = slice msg (16 - length st.pmsg) (length msg) in
    lemma_eq_intro nmsg createEmpty;
    let nacc = (st.acc +@ (encode block)) *@ st.r in
    let nst = MkState st.r nacc createEmpty in
    lemma_gmac_update_empty nst
  end else begin
    lemma_eq_intro (reveal_sbytes msg) (st.pmsg @| reveal_sbytes msg)
  end

val lemma_gmac_spec_short: msg:sbytes{length msg < 16} -> r:skey -> Lemma
  (requires True)
  (ensures (
    let st_0 = gmac_init_spec r in
    let st = gmac_update_spec st_0 msg in
    gmac_last_spec st = poly (encode_bytes (reveal_sbytes msg)) (encode (reveal_sbytes r))))
let lemma_gmac_spec_short msg r =
  let st_0 = gmac_init_spec r in
  let st = gmac_update_spec st_0 msg in
  if length msg = 0 then begin
    lemma_gmac_update_empty st_0;
    lemma_eq_intro msg createEmpty
  end else begin
    lemma_eq_intro st_0.pmsg createEmpty;
    lemma_eq_intro (st_0.pmsg @| reveal_sbytes msg) (reveal_sbytes msg);
    lemma_encode_bytes_0 createEmpty (reveal_sbytes msg);
    lemma_eq_intro (createEmpty @| msg) msg;
    lemma_eq_intro (encode_bytes createEmpty) createEmpty;
    poly_cons (reveal_sbytes msg) (encode_bytes createEmpty) (encode (reveal_sbytes r));
    add_comm (encode (reveal_sbytes msg)) zero
  end

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_gmac_spec_: msg:sbytes -> r:skey -> Lemma
  (requires True)
  (ensures (
    let st_0 = gmac_init_spec r in
    let st = gmac_update_spec st_0 msg in
    gmac_last_spec st = poly (encode_bytes (reveal_sbytes msg)) (encode (reveal_sbytes r))))
  (decreases (length msg))
let rec lemma_gmac_spec_ msg r = 
  let st_0 = gmac_init_spec r in
  let st = gmac_update_spec st_0 msg in
  if length msg < 16 then lemma_gmac_spec_short msg r
  else begin
    let ltl = (length msg + 15) % 16 + 1 in
    let lhd = length msg - ltl in
    let hd, tl = split msg lhd in
    lemma_split msg lhd;
    lemma_eq_intro (reveal_sbytes msg) (reveal_sbytes hd @| reveal_sbytes tl);
    lemma_encode_bytes (reveal_sbytes hd) (reveal_sbytes tl);
    poly_cons (reveal_sbytes tl) (encode_bytes (reveal_sbytes hd)) (encode (reveal_sbytes r));
    lemma_gmac_spec_ hd r;
    lemma_gmac_update_ st_0 hd tl;
    let st' = gmac_update_spec st_0 hd in
    lemma_gmac_update_last st' tl;
    add_comm (encode (reveal_sbytes tl)) (poly (encode_bytes (reveal_sbytes hd)) (encode (reveal_sbytes r)))
  end


(* Important proprieties *)

#reset-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

val lemma_gmac_update: st:gmac_state_ -> msgs:seq sbytes -> Lemma
  (requires True)
  (ensures (gmac_update_spec_repeat st msgs = gmac_update_spec st (flatten_sbytes msgs)))
  (decreases (length msgs))
let rec lemma_gmac_update st msgs = 
  if length msgs = 0 then begin
    lemma_eq_intro st.pmsg (st.pmsg @| createEmpty)
  end else begin
    lemma_gmac_update (gmac_update_spec st (head msgs)) (tail msgs);
    lemma_gmac_update_ st (head msgs) (flatten_sbytes (tail msgs))
  end

val lemma_gmac_spec: msg:sbytes -> r:skey -> s:stag -> Lemma
  (requires True)
  (ensures (gmac_spec msg r s =
    mac (encode_bytes (reveal_sbytes msg)) (encode (reveal_sbytes r)) (reveal_sbytes s)))
let lemma_gmac_spec msg r s = lemma_gmac_spec_ msg r
