module Hacl.Spec.GMAC

module Spec = Spec.GF128

open Spec

open FStar.Seq
open FStar.Endianness

type gmac_state_ = | MkState: r:elem -> acc:elem -> pmsg:bytes{length pmsg < 16} -> gmac_state_

#set-options "--z3rlimit 20 --initial_fuel 0 -0max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let gmac_alloc_spec : gmac_state_ = MkState zero zero createEmpty

val gmac_init_spec: r:key -> GTot gmac_state_
let gmac_init_spec r = MkState (encode r) zero createEmpty

val gmac_update_spec_nopmsg: cst:gmac_state_{length cst.pmsg = 0} -> msg:bytes ->
  GTot gmac_state_ (decreases (length msg))
let rec gmac_update_spec_nopmsg cst msg =
  if length msg >= 16 then begin
    let block : word = slice msg 0 16 in
    let nmsg : bytes = slice msg 16 (length msg) in
    let nacc = (cst.acc +@ (encode block)) *@ cst.r in
    let nst = MkState cst.r nacc cst.pmsg in
    gmac_update_spec_nopmsg nst nmsg
  end else begin
    MkState cst.r cst.acc msg
  end

val gmac_update_spec_wpmsg: cst:gmac_state_{length cst.pmsg > 0} -> msg:bytes ->
  GTot gmac_state_
let gmac_update_spec_wpmsg cst msg =
  if length msg + length cst.pmsg >= 16 then begin
    let block : word = cst.pmsg @| (slice msg 0 (16 - length cst.pmsg)) in
    let nmsg : bytes = slice msg (16 - length cst.pmsg) (length msg) in
    let nacc = (cst.acc +@ (encode block)) *@ cst.r in
    let nst = MkState cst.r nacc createEmpty in
    gmac_update_spec_nopmsg nst nmsg
  end else begin
    MkState cst.r cst.acc (cst.pmsg @| msg)
  end

val gmac_update_spec: cst:gmac_state_ -> msg:bytes -> GTot gmac_state_
let gmac_update_spec cst msg =
  if length cst.pmsg = 0 then gmac_update_spec_nopmsg cst msg
  else gmac_update_spec_wpmsg cst msg

val gmac_last_spec: cst:gmac_state_ -> GTot gmac_state_
let gmac_last_spec cst =
  let block : word = pad cst.pmsg in
  let nacc = (cst.acc +@ (encode block)) *@ cst.r in
  MkState cst.r nacc createEmpty

val gmac_finish_spec: cst:gmac_state_ -> s:tag -> GTot tag
let gmac_finish_spec cst s =
  let nst = gmac_last_spec cst in
  let nacc = (nst.acc +@ (encode s)) *@ nst.r in
  decode nacc

val gmac_spec: msg:bytes -> r:key -> s:tag -> 
  GTot (t:tag{t = mac (encode_bytes msg) (encode r) s})
let gmac_spec msg r s =
  admit();
  let st = gmac_init_spec r in
  let st = gmac_update_spec st msg in
  gmac_finish_spec st s
  

val flatten_bytes: msgs:seq bytes -> Tot bytes (decreases (length msgs))
let rec flatten_bytes msgs =
  if length msgs = 0 then createEmpty
  else (head msgs) @| (flatten_bytes (tail msgs))
  
val gmac_update_spec_repeat: cst:gmac_state_ -> msgs:seq bytes -> GTot gmac_state_ (decreases (length msgs))
let rec gmac_update_spec_repeat cst msgs =
  if length msgs = 0 then cst
  else
    let nst = gmac_update_spec cst (head msgs) in
    gmac_update_spec_repeat nst (tail msgs)
    
val lemma_gmac_update: st:gmac_state_ -> msgs:seq bytes -> Lemma
  (requires True)
  (ensures (gmac_update_spec_repeat st msgs = gmac_update_spec st (flatten_bytes msgs)))
let lemma_gmac_update st msgs = admit()
