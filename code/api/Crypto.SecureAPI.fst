module Crypto.SecureAPI

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 100"

let poly1305_state = Hacl.Impl.Poly1305_64.poly1305_state

let mk_state r h  = Hacl.Impl.Poly1305_64.mk_state r h

let get_r s = Hacl.Impl.Poly1305_64.(s.r)
let get_h s = Hacl.Impl.Poly1305_64.(s.h)

let red_44 s = Hacl.Spec.Bignum.AddAndMultiply.red_44 s

let red_45 s = Hacl.Spec.Bignum.AddAndMultiply.red_44 s

let seval s = Hacl.Spec.Poly1305_64.seval s

let selem s = Hacl.Spec.Poly1305_64.selem s

[@"substitute"]
let poly1305_start a = Hacl.Impl.Poly1305_64.poly1305_start a

[@"substitute"]
let poly1305_encode_r r key =
  Hacl.Impl.Poly1305_64.poly1305_encode_r r key

#reset-options "--max_fuel 0 --z3rlimit 200"

[@"c_inline"]
let poly1305_update current_log st m =
  let h0 = ST.get() in
  let updated_log = Hacl.Impl.Poly1305_64.poly1305_update current_log st m in
  let h1 = ST.get() in
  assert(modifies_1 (get_h st) h0 h1);
  assert(live_st h1 st);
  assert(red_44 (as_seq h1 (get_h st)));
  assert(selem (as_seq h1 (get_r st)) == selem (as_seq h0 (get_r st)));
  assert(let acc0 = selem (as_seq h0 (get_h st)) in
         let acc1 = selem (as_seq h1 (get_h st)) in
         let r0 = selem (as_seq h0 (get_r st)) in
         let block  = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 m) + pow2 128 in
         acc1  = Spec.Poly1305.((acc0 +@ block) *@ r0));
  assert(let acc0 = selem (as_seq h0 (get_h st)) in
         let acc1 = selem (as_seq h1 (get_h st)) in
         let r0 = selem (as_seq h0 (get_r st)) in
         let r1 = selem (as_seq h1 (get_r st)) in
         let log0 = Ghost.reveal current_log in
         let log1 = Ghost.reveal updated_log in
         let block  = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 m) + pow2 128 in
         (log1 == FStar.Seq.((create 1 (Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 m))) @| log0)));
  admit();
  updated_log


[@"substitute"]
let poly1305_finish_ log st mac m len key_s =
  Hacl.Impl.Poly1305_64.poly1305_finish_ log st mac m len key_s

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let poly_def_0 log r  = ()

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

let poly_def_1 log r = ()

#reset-options "--max_fuel 0 --z3rlimit 50"

open Hacl.Impl.Chacha20
open Hacl.Lib.LoadStore32

[@ "substitute"]
let setup st k n c = setup st k n c

[@ "substitute"]
let chacha20_core k st =
  copy_state k st;
  rounds k;
  sum_states k st

[@ "substitute"]
let chacha20_stream stream_block st =
  push_frame();
  let h_0 = ST.get() in
  let st' = Buffer.create (Hacl.Cast.uint32_to_sint32 0ul) 16ul in
  let log' = chacha20_core st' st in
  uint32s_to_le_bytes stream_block st' 16ul;
  let h = ST.get() in
  cut (modifies_2_1 stream_block h_0 h);
  pop_frame()

[@ "substitute"]
let chacha20_stream_finish stream_block len st =
  push_frame();
  let b = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  chacha20_stream b st;
  blit b 0ul stream_block 0ul len;
  pop_frame()
