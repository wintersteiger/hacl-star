module Hacl.Spec.GMAC

module Spec = Spec.GF128

open Spec

open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness

noeq type gmac_state_ = | MkState: r:elem -> s:tag -> acc:elem -> pmsg:bytes{length pmsg < 16} -> gmac_state_

val gmac_init_spec: r:word_16 -> s:tag -> GTot gmac_state_
let gmac_init_spec r s = MkState (encode r) s zero createEmpty

val gmac_update_spec: cst:gmac_state_ -> msg:bytes -> GTot gmac_state_
