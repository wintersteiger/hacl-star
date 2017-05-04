module Spec.Sbox

open FStar.Seq
open FStar.BitVector

let gf8_elem = bv_t 8
let gf4_elem = bv_t 4
let gf2_elem = bv_t 2


let mk_gf2_elem (x:bool) (y:bool) : gf2_elem = createL [x; y]
let mk_gf4_elem (x:gf2_elem) (y:gf2_elem) : gf4_elem = append x y
let mk_gf8_elem (x:gf4_elem) (y:gf4_elem) : gf8_elem = append x y
let sp_gf2_elem (x:gf2_elem) : bool * bool = index x 0, index x 1
let sp_gf4_elem (x:gf4_elem) : gf2_elem * gf2_elem = slice x 0 2, slice x 2 4
let sp_gf8_elem (x:gf8_elem) : gf4_elem * gf4_elem = slice x 0 4, slice x 4 8


let gf2_add x y = logxor_vec #2 x y

let gf2_mul x y =
  let a, b = sp_gf2_elem x in
  let c, d = sp_gf2_elem y in
  let e = (a <> b) && (c <> d) in
  let p = (a && c) <> e in
  let q = (b && d) <> e in
  mk_gf2_elem p q

let gf2_scale_N x =
  let a, b = sp_gf2_elem x in
  mk_gf2_elem b (a <> b)

let gf2_scale_N2 x =
  let a, b = sp_gf2_elem x in
  mk_gf2_elem (a <> b) a

let gf2_sq x = gf2_mul x x

let gf2_inv x = gf2_sq x


let gf4_add x y = logxor_vec #4 x y

let gf4_mul x y =
  let a, b = sp_gf4_elem x in
  let c, d = sp_gf4_elem y in
  let e = gf2_scale_N (gf2_mul (gf2_add a b) (gf2_add c d)) in
  let p = gf2_add e (gf2_mul a c) in
  let q = gf2_add e (gf2_mul b d) in
  mk_gf4_elem p q

let gf4_sq_scale x =
  let a, b = sp_gf4_elem x in
  let p = gf2_sq (gf2_add a b) in
  let q = gf2_scale_N2 (gf2_sq b) in
  mk_gf4_elem p q

let gf4_inv x =
  let a, b = sp_gf4_elem x in
  let c = gf2_scale_N (gf2_sq (gf2_add a b)) in
  let d = gf2_mul a b in
  let e = gf2_inv (gf2_add c d) in
  let p = gf2_mul e b in
  let q = gf2_mul e a in
  mk_gf4_elem p q


let gf8_add x y = logxor_vec #8 x y

let gf8_inv x =
  let a, b = sp_gf8_elem x in
  let c = gf4_sq_scale (gf4_add a b) in
  let d = gf4_mul a b in
  let e = gf4_inv (gf4_add c d) in
  let p = gf4_mul e b in
  let q = gf4_mul e a in
  mk_gf8_elem p q


type trans_mat = s:seq (UInt.uint_t 8){length s = 8}

let a2x : trans_mat = createL [0x98; 0xF3; 0xF2; 0x48; 0x09; 0x81; 0xA9; 0xFF]
let x2a : trans_mat = createL [0x64; 0x78; 0x6E; 0x8C; 0x68; 0x29; 0xDE; 0x60]
let x2s : trans_mat = createL [0x58; 0x2D; 0x9E; 0x0B; 0xDC; 0x04; 0x03; 0x24]
let s2x : trans_mat = createL [0x8C; 0x79; 0x05; 0xEB; 0x12; 0x04; 0x51; 0x53]

val gf8_newbasis_loop: x:gf8_elem -> m:trans_mat -> i:int{i < 8} -> Tot gf8_elem (decreases (i + 1))
let rec gf8_newbasis_loop x m i=
  if i < 0 then zero_vec #8 else begin
    if index x i then gf8_add (UInt.to_vec #8 (index m i)) (gf8_newbasis_loop x m (i - 1)) else gf8_newbasis_loop x m (i - 1)
  end
  
let gf8_newbasis x m = gf8_newbasis_loop x m 7

let sbox_b : gf8_elem = UInt.to_vec #8 0x63

let sbox x =
  let t = gf8_newbasis x a2x in
  let t = gf8_inv t in
  let t = gf8_newbasis t x2s in
  gf8_add t sbox_b
  
let inv_sbox x =
  let t = gf8_newbasis (gf8_add x sbox_b) s2x in
  let t = gf8_inv t in
  let t = gf8_newbasis t x2a in
  t


let test() =
  UInt.from_vec #8 (sbox (UInt.to_vec #8 157)) = 94
  && UInt.from_vec #8 (inv_sbox (UInt.to_vec #8 94)) = 157
