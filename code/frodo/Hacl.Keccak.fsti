module Hacl.Keccak

open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Modifies

open Hacl.Impl.PQ.Lib

module B = Lib.Buffer

val cshake128_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> B.live h input /\ B.live h output /\ B.disjoint input output))
  (ensures (fun h0 _ h1 -> B.live h1 output /\ modifies (loc_buffer output) h0 h1))

val cshake256_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> B.live h input /\ B.live h output /\ B.disjoint input output))
  (ensures (fun h0 _ h1 -> B.live h1 output /\ modifies (loc_buffer output) h0 h1))
