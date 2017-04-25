module Crypto.SecureAPI

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

let text  = Spec.Poly1305.text
let elem  = Spec.Poly1305.elem
let log_t = Ghost.erased text
let elemB = b:buffer Hacl.UInt64.t{length b = 3}

val poly1305_state: Type0

val mk_state: r:elemB -> h:elemB -> Tot poly1305_state

val get_r: poly1305_state -> Tot elemB
val get_h: poly1305_state -> Tot elemB

let live_st m (st:poly1305_state) : GTot Type0 =
  live m (get_h st) /\ live m (get_r st) /\ disjoint (get_h st) (get_r st)

val red_44:
  s:Seq.seq Hacl.UInt64.t{Seq.length s = 3} ->
  GTot Type0

val red_45:
  s:Seq.seq Hacl.UInt64.t{Seq.length s = 3} ->
  GTot Type0

val seval:
  s:Seq.seq Hacl.UInt64.t{Seq.length s = 3} ->
  GTot nat

val selem:
  s:Seq.seq Hacl.UInt64.t{Seq.length s = 3} ->
  GTot Spec.Poly1305.elem


[@"substitute"]
val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      /\ red_45 (as_seq h1 a)
      /\ selem (as_seq h1 a) == 0
      /\ seval (as_seq h1 a) == 0
      ))

[@"substitute"]
val poly1305_encode_r:
  r:elemB ->
  key:buffer Hacl.UInt8.t{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      /\ seval (as_seq h1 r) == UInt.logand #128 (Hacl.Spec.Endianness.hlittle_endian (as_seq h0 key))
                                                0x0ffffffc0ffffffc0ffffffc0fffffff
    ))


[@"c_inline"]
val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:buffer Hacl.UInt8.t{length m = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ live h (get_r st) /\ live h (get_h st)
      /\ red_45 (as_seq h (get_h st))
      /\ red_44 (as_seq h (get_r st))
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_h st) h0 h1 /\ live_st h1 st /\ live_st h0 st
      /\ live h0 m
      /\ red_45 (as_seq h0 (get_h st))
      /\ red_44 (as_seq h0 (get_r st))
      /\ red_45 (as_seq h1 (get_h st))
      /\ (let acc0 = seval (as_seq h0 (get_h st)) in
         let acc1 = seval (as_seq h1 (get_h st)) in
         let r0 = seval (as_seq h0 (get_r st)) in
         let r1 = seval (as_seq h1 (get_r st)) in
         let log0 = Ghost.reveal current_log in
         let log1 = Ghost.reveal updated_log in
         let block  = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 m) + pow2 128 in
         r0 = r1 /\ acc1 % Spec.Poly1305.prime = ((acc0 + block) * r0) % Spec.Poly1305.prime
         /\ (log1 == FStar.Seq.((create 1 (Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 m))) @| log0)))
      ))


[@"substitute"]
val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:buffer Hacl.UInt8.t{length mac = 16} ->
  m:buffer Hacl.UInt8.t ->
  len:FStar.UInt64.t{UInt64.v len < 16 /\ UInt64.v len = length m} ->
  key_s:buffer Hacl.UInt8.t{length key_s = 16} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint (get_h st) mac /\ disjoint (get_h st) key_s /\ disjoint (get_h st) m
      /\ red_44 (as_seq h (get_r st)) /\ red_45 (as_seq h (get_h st))))
    (ensures  (fun h0 updated_log h1 -> modifies_2 (get_h st) mac h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 (get_h st) /\ live h1 mac /\ live h0 key_s
      /\ red_44 (as_seq h0 (get_r st)) /\ red_45 (as_seq h0 (get_h st))
      /\ (let acc = seval (as_seq h0 (get_h st)) in
         let r   = seval (as_seq h0 (get_r st)) in
         let k   = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 key_s)   in
         let m'   = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 m) + pow2 (8*length m) in
         let m    = as_seq h0 m in
         let mac = Hacl.Spec.Endianness.hlittle_endian (as_seq h1 mac) in
         if Seq.length m >= 1
         then mac = (((((acc + m') * r) % Spec.Poly1305.prime)) + k) % pow2 128
         else mac = ((((acc % Spec.Poly1305.prime) ) + k) % pow2 128))
    ))

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val poly_def_0: log:text{Seq.length log = 0} -> r:elem -> Lemma (Spec.Poly1305.poly log r = 0)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val poly_def_1: log:text{Seq.length log > 0} -> r:elem -> Lemma
  (let hd = Seq.head log in
   let tl = Seq.tail log in
   Spec.Poly1305.poly log r = Spec.Poly1305.((poly tl r +@ encode hd) *@ r))


let state = b:buffer Hacl.UInt32.t{length b = 16}
let uint8_p = buffer Hacl.UInt8.t

[@ "substitute"]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:UInt32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1))

[@ "substitute"]
val chacha20_core:
  k:state ->
  st:state{disjoint st k} ->
  Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h0 st /\ live h0 k
      /\ live h1 k /\ live h1 st /\ modifies_1 k h0 h1))


[@ "substitute"]
val chacha20_stream:
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))


[@ "substitute"]
val chacha20_stream_finish:
  stream_block:uint8_p ->
  len:UInt32.t{UInt32.v len <= 64 /\ length stream_block = UInt32.v len} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))
