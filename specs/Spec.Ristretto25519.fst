module Spec.Ristretto25519

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Curve25519

(* Field types and parameters *)
let prime : pos = pow2 252 + 27742317777372353535851937790883648493
type elem = x:nat{x < prime}
type jacb_point = elem & elem & elem & elem


let fadd (x:elem) (y:elem) : elem = (x + y) % prime
let fsub (x:elem) (y:elem) : elem = (x - y) % prime
let fmul (x:elem) (y:elem) : elem = (x * y) % prime

let ( +% ) = fadd
let ( -% ) = fsub
let ( *% ) = fmul

val fpow: a:elem -> b:pos -> Tot elem (decreases b)
let rec fpow a b =
  if b = 1 then a
  else
    if b % 2 = 0 then fpow (a *% a) (b / 2)
    else a *% (fpow (a *% a) (b / 2))

let ( **% ) = fpow



let d : elem = 37095705934669439343138083508754565189542113879843219016388785533085940283555
let sqrt_m1 : elem = 19681161376707505956807079304988542015446066515923890162744021073123829784752
let sqrt_ad_minus_one : elem = 25063068953384623474111414158702152701244531502492656460079210482610430750235
let inv_sqrt_a_minus_d : elem = 54469307008909316920995813868745141605393597292927456921205312896311721017578
let one_minus_d_sq : elem = 1159843021668779879193775521855586647937357759715417654439879720876111806838
let d_minus_one_sq : elem = 40440834346308536858101042469323190826248399146238708352240133220865137265952


let is_zero (e:elem) = if e = 0 then true else false
assume val is_negative: elem -> Tot bool
assume val is_square: elem -> Tot bool
assume val sqrt: elem -> Tot elem
assume val neg: elem -> Tot elem


val sqrt_ratio_m1: elem -> elem -> Tot (bool & elem)
let sqrt_ratio_m1 u v =
  let v3 = (v **% 2) *% v in
  let v7 = (v3 **% 2) *% v in
  let r = (u *% v3) *% ((u *% v7 ) **% (prime - 5) / 8) in
  let check: elem = v *% (r **% 2) in

  let correct_sign_sqrt: bool = check = u in
  let flipped_sign_sqrt: bool = check = (neg u) in
  let flipped_sign_sqrt_i: bool = check = (neg u *% sqrt_m1) in

  let r_prime = sqrt_m1 *% r in
  let r = if flipped_sign_sqrt || flipped_sign_sqrt_i then r_prime else r in
  let r = abs r in

  let was_square = correct_sign_sqrt || flipped_sign_sqrt in
  (was_square, r)


let decodePoint (u:serialized_point) : Tot (option jacb_point) =
  let s =  (nat_from_bytes_le u % pow2 255) % prime in
  let ss = s **% 2 in
  let u1 = 1 + (neg ss) in
  let u2 = 1 + ss in
  let u2_sqr = u2 **% 2 in
  let v = neg (d *% (u1 **% 2)) + neg u2_sqr in
  let was_square, invsqrt = sqrt_ratio_m1 1 (v *% u2_sqr) in
  let den_x = invsqrt *% 2 in
  let den_y = invsqrt *% den_x *% v in
  let x = abs (2 *% s *% den_x) in
  let y = u1 *% den_y in
  let t = x *% y in
  Some (x, y, 1, t)


let encodePoint (p:jacb_point) : Tot serialized_point =
  let x0, y0, z0, t0 = p in
  let u1 = (x0 +% y0) *% (z0 - y0) in
  let u2 = x0 *% y0 in
  let _,invsqrt = sqrt_ratio_m1 1 (u1 *% (u2 **% 2)) in
  let den1 = invsqrt *% u1 in
  let den2 = invsqrt *% u2 in
  let z_inv = den1 *% den2 *% t0 in
  let ix0 = x0 *% sqrt_m1 in
  let iy0 = y0 *% sqrt_m1 in
  let x, y, den_inv = if is_negative (t0 *% z_inv) then iy0, ix0, (den1 *% inv_sqrt_a_minus_d) else x0, y0, den2 in
  let z = z0 in
  let y = if is_negative (x *% z_inv) then neg y else y in
  let s = abs (den_inv *% (z +% neg y)) in
  nat_to_bytes_le 32 (s % prime)


let equalPoint (p1:jacb_point) (p2:jacb_point) : Tot bool =
  let x1,y1,_,_ = p1 in
  let x2,y2,_,_ = p2 in
  (x1 *% y2 = y1 *% x2) || (y1 *% y2 = x1 *% x2)


let map (b:lbytes 64) : Tot jacb_point =
  let t =  (nat_from_bytes_le b % pow2 255) % prime in
  let r = sqrt_m1 *% (t **% 2) in
  let u = (r +% 1) *% one_minus_d_sq in
  let v = (neg 1 +% neg (r *% d)) *% (r +% d) in
  let was_square, s = sqrt_ratio_m1 u v in
  let s_prime = neg (abs (s *% t)) in
  let s, c = if was_square then s, neg 1 else s_prime, r in
  let n = c *% (r +% neg 1) *% d_minus_one_sq + neg v in
  let w0 = 2 *% s *% v in
  let w1 = n *% sqrt_ad_minus_one in
  let w2 = 1 + neg (s **% 2) in
  let w3 = 1 + (s **% 2) in
  (w0 *% w3, w2 *% w1, w1 *% w3, w0 *% w2)
