module Hacl.Impl.Blake2b.Incremental

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

open Hacl.Impl.Blake2b
open Spec.Blake2.Incremental

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module LBS = Lib.ByteSequence

module Spec = Spec.Blake2
module SpecI = Spec.Blake2.Incremental


#set-options "--z3rlimit 200 --max_fuel 0"


(** Define the state *)
noeq type state_r = {
  hash: hash_wp;
  n: size_t;
  pl: l:size_t{v l <= v size_block};
  block: block_p;
}


unfold let state_inv (h:mem) (state:state_r) =
  live h state.hash /\ live h state.block /\ disjoint state.hash state.block

unfold let state_empty (h:mem) (state:state_r) =
  h.[|state.hash|] == Seq.create Spec.size_hash_w (u64 0) /\
  v state.n == 0 /\
  v state.pl == 0 /\
  h.[|state.block|] == Seq.create (Spec.size_block Spec.Blake2B) (u8 0)

val state_hash_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_hash_eq h istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|]

val state_block_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_block_eq h istate sstate =
  sstate.SpecI.block == h.[|istate.block|]

val state_eq: h:mem -> state_r -> (SpecI.state_r Spec.Blake2B) -> prop
let state_eq h istate sstate =
  sstate.SpecI.hash == h.[|istate.hash|] /\
  sstate.SpecI.n == v istate.n /\
  sstate.SpecI.pl == v istate.pl /\
  sstate.SpecI.block == h.[|istate.block|]


val spec_of: h:mem -> state_r -> GTot (SpecI.state_r Spec.Blake2B)
let spec_of h state =
  let hash: Spec.hash_ws Spec.Blake2B = h.[|state.hash|] in
  let n: size_nat = v state.n in
  let pl: l:size_nat{l <= Spec.size_block Spec.Blake2B} = v state.pl in
  let block: Spec.block_s Spec.Blake2B = h.[|state.block|] in
  Spec.Blake2.Incremental.Mkstate_r hash n pl block


val blake2b_incremental_init:
    state: state_r
  -> kk: size_t{v kk <= 64}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 64} ->
  Stack state_r
  (requires fun h ->
    live h state.hash /\ live h k /\
    disjoint state.hash k /\
    state_inv h state /\
    state_empty h state)
  (ensures  fun h0 rstate h1 ->
    modifies1 state.hash h0 h1 /\
    spec_of h1 rstate == SpecI.blake2_incremental_init Spec.Blake2B h0.[|k|] (v nn))

let blake2b_incremental_init state kk k nn =
  blake2b_init state.hash kk k nn;
  let n = if kk =. 0ul then 0ul else 1ul in
  let rstate = { state with n = n; } in
  rstate



val spec_blake2_incremental_update_first:
    block:Spec.block_s Spec.Blake2B
  -> pl: size_nat{pl <= Spec.size_block Spec.Blake2B}
  -> ll: size_nat
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s Spec.Blake2B)

let spec_blake2_incremental_update_first block pl ll input =
  let rb = Spec.size_block Spec.Blake2B - pl in
  let ll0 = if ll < rb then ll else rb in
  let partial = Seq.sub #uint8 #ll input 0 ll0 in
  Seq.update_sub block pl ll0 partial


val blake2b_incremental_update_first:
    block:block_p
  -> pl:size_t{v pl <= v size_block}
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_first h0.[|block|] (v pl) (v ll) h0.[|input|])

let blake2b_incremental_update_first block pl ll input =
  let rb = size_block -! pl in
  let ll0 = if ll <. rb then ll else rb in
  let partial = sub input 0ul ll0 in
  update_sub #MUT #uint8 #size_block block pl ll0 partial



val spec_blake2_incremental_update_loop:
  n:size_nat
  -> blocks:LBS.bytes{Seq.length blocks <= max_size_t /\ (n + (Seq.length blocks / (Spec.size_block Spec.Blake2B))) * (Spec.size_block Spec.Blake2B) <= pow2 128 - 1}
  -> hash:Spec.hash_ws Spec.Blake2B ->
  Tot (Spec.hash_ws Spec.Blake2B)

let spec_blake2_incremental_update_loop ni blocks hash =
  let n = Seq.length blocks / Spec.size_block Spec.Blake2B in
  repeati n (fun i hash ->
    let block = Seq.sub #uint8 #(Seq.length blocks) blocks (i * Spec.size_block Spec.Blake2B) (Spec.size_block Spec.Blake2B) in
      Spec.blake2_update_block Spec.Blake2B ((ni + i + 1) * Spec.size_block Spec.Blake2B) block hash
    ) hash


val blake2b_incremental_update_loop:
    state:state_r
  -> n:size_t
  -> blocks:lbuffer uint8 (n *. size_block) ->
  Stack unit
  (requires fun h ->
    state_inv h state /\ live h blocks /\
    disjoint state.hash blocks /\ disjoint state.block blocks /\
    state_inv h state /\
    v n * v size_block <= max_size_t /\
    v ((state.n +. n) *. size_block) <= pow2 128 - 1)
  (ensures  fun h0 _ h1 ->
    modifies2 state.hash state.block h0 h1)

let blake2b_incremental_update_loop state n blocks =
  let h0 = ST.get () in
  (* [@inline_let] *)
  (* let spec h = (fun i s -> ) in *)
  loop_nospec #h0 n state.hash
  (fun i ->
    (* Loops.unfold_repeati (v n) (spec h0) h0.[|state.hash|] (v i); *)
    let block = sub blocks (i *. size_block) size_block in
    let n64 = to_u64 state.n in
    let i64 = to_u64 i in
    let size_block64 = to_u64 size_block in
    let prev = to_u128 ((n64 +! i64 +! (u64 1)) *! size_block64) in
    blake2b_update_block state.hash prev block)


val spec_blake2_incremental_update_end:
    block:Spec.block_s Spec.Blake2B
  -> ll: size_nat
  -> ll0: size_nat{ll0 < ll}
  -> input: Seq.lseq uint8 ll ->
  Tot (Spec.block_s Spec.Blake2B)

let spec_blake2_incremental_update_end block ll ll0 input =
  let ll2 = (ll - ll0) % (Spec.size_block Spec.Blake2B) in
  let input2 = Seq.sub #uint8 #ll input (ll - ll2) ll2 in
  Seq.update_sub block 0 ll2 input2


val blake2b_incremental_update_end:
    block:block_p
  -> ll:size_t
  -> ll0:size_t{v ll0 < v ll}
  -> input:lbuffer uint8 ll ->
  Stack unit
  (requires fun h ->
    live h block /\ live h input /\
    disjoint block input)
  (ensures  fun h0 _ h1 ->
    modifies1 block h0 h1 /\
    h1.[|block|] == spec_blake2_incremental_update_end h0.[|block|] (v ll) (v ll0) h0.[|input|])

let blake2b_incremental_update_end block ll ll0 input =
  let ll2 = (ll -. ll0) %. size_block in
  let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in
  update_sub block 0ul ll2 input2



inline_for_extraction
val blake2b_incremental_update:
    state:state_r
  -> ll:size_t
  -> input:lbuffer uint8 ll ->
  Stack state_r
  (requires fun h ->
    state_inv h state /\ live h input /\
    disjoint state.hash input /\ disjoint state.block input /\
    state_inv h state /\
    v (state.n *. size_block) + v ll < pow2 128)
  (ensures  fun h0 _ h1 ->
    modifies2 state.hash state.block h0 h1)

let blake2b_incremental_update state ll input =
  let nll = ll /. size_block in
  if ll =. 0ul || not (state.n +. nll +. 2ul <=. size 0xFFFFFFFF) then state else (
  let rb = size_block -. state.pl in
  let ll0 = if ll <. rb then ll else rb in
  let partial = sub input 0ul ll0 in
  update_sub #MUT #uint8 #size_block state.block state.pl ll0 partial;
  if ll <=. rb then ({state with pl = state.pl +. ll0})
  else (
    let prev = to_u128 ((state.n +. 1ul) *. size_block) in
    blake2b_update_block state.hash prev state.block;
    (* Handle all full blocks available *)
    let n1 = (ll -. ll0) /. size_block in
    let input1 = sub input ll0 (ll -. ll0) in
    let h0 = ST.get () in
    loop_nospec #h0 n1 state.hash
    (fun i ->
      let block = sub input1 (i *. size_block) size_block in
      let h1 = ST.get () in
      let prev = to_u128 (secret ((state.n +. i +. 1ul) *. size_block)) in
      blake2b_update_block state.hash prev block);
    let state = {state with n = state.n +. n1;} in
    (* Store the remainder *)
    let ll2 = (ll -. ll0) %. size_block in
    let input2 = sub #MUT #uint8 #ll input (ll -. ll2) ll2 in
    let block = update_sub state.block 0ul ll2 input2 in
    ({state with pl = ll2;})
  ))



val blake2b_incremental_finish:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output:lbuffer uint8 nn
  -> state:state_r ->
  Stack unit
    (requires fun h ->
      state_inv h state /\ live h output /\
      disjoint output state.hash /\
      state_inv h state)
    (ensures  fun h0 _ h1 ->
      modifies2 output state.hash h0 h1 /\
      h1.[|output|] == Spec.Blake2.Incremental.blake2_incremental_finish Spec.Blake2.Blake2B (spec_of h0 state) (v nn))


let blake2b_incremental_finish nn output state =
  let h0 = ST.get () in
  let last = sub state.block 0ul state.pl in
  let n64 = to_u64 state.n in
  let size_block64 = to_u64 size_block in
  let pl64 = to_u64 state.pl in
  let prev = to_u128 (n64 *! size_block64 +! pl64) in
  assert(v prev = (spec_of h0 state).SpecI.n * (Spec.Blake2.size_block Spec.Blake2.Blake2B) + (spec_of h0 state).SpecI.pl);
  blake2b_update_last state.hash prev state.pl last;
  blake2b_finish nn output state.hash
