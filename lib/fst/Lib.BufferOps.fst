module Lib.BufferOps

(* Handy notations for Lib.Buffer, so users can open this module
   instead of the whole Lib.Buffer, to just bring these operators
   and notations into the scope without bringing any definition from
   Lib.Buffer into the scope. *)

module HST = FStar.HyperStack.ST

module B   = Lib.Buffer
module Int = Lib.IntTypes
module RI  = Lib.RawIntTypes
module Seq = Lib.Sequence
module M   = Lib.Modifies

module BO  = LowStar.BufferOps

module MP  = LowStar.ModifiesPat

let ( !* ) #a p =
  BO.op_Bang_Star #a p
  
let ( *= ) #a p v = 
  B.upd p (Int.size 0) v

let blit #t src idx_src dst idx_dst len =
  let h0 = HST.get () in
  BO.blit #t src 
    (RI.size_to_UInt32 idx_src)
    dst 
    (RI.size_to_UInt32 idx_dst) 
    (RI.size_to_UInt32 len);
  let h1 = HST.get () in
  assert (LowStar.Modifies.(modifies (loc_buffer dst) h0 h1));
  assert (LowStar.Modifies.(modifies (loc_buffer dst) h0 h1) ==
          M.modifies (M.loc_buffer dst) h0 h1)
