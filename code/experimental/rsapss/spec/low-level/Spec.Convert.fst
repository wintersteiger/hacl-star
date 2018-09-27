module Spec.Convert

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let lbignum len = lseq uint64 len
let lbytes len = lseq uint8 len

let size_pos = x:size_nat{x > 0}

let blocks (x:size_nat) (m:size_pos): (r:size_nat{x <= m * r}) =
  if x < 1 then 0
  else (x - 1) / m + 1

val text_to_nat_:
    len:size_pos
  -> input:lbytes len
  -> resLen:size_pos{len == 8 * resLen}
  -> res:lbignum resLen
  -> lbignum resLen
let text_to_nat_ len input resLen res =
  repeati resLen
  (fun i res ->
    let inputi = uint_from_bytes_be #U64 (sub input (8 * i) 8) in
    res.[resLen - i - 1] <- inputi
  ) res

val text_to_nat:
    len:size_pos{8 * blocks len 8 < max_size_t}
  -> input:lbytes len
  -> lbignum (blocks len 8)
let text_to_nat len input =
  let resLen = blocks len 8 in
  let res = create resLen (u64 0) in
  let tmpLen = 8 * resLen in
  let tmp = create tmpLen (u8 0) in

  let m = len % 8 in
  let ind = if m = 0 then 0 else 8 - m in
  admit();
  let tmp = update_sub tmp ind (tmpLen - ind) input in
  text_to_nat_ tmpLen tmp resLen res

val nat_to_text_:
    len:size_pos
  -> input:lbignum len
  -> resLen:size_pos{resLen == 8 * len}
  -> res:lbytes resLen
  -> lbytes resLen
let nat_to_text_ len input resLen res =
  repeati len
  (fun i res ->
    let tmp = input.[len - i - 1] in
    update_sub res (8 * i) 8 (uint_to_bytes_be tmp)
  ) res

val nat_to_text:
    len:size_pos
  -> input:lbignum (blocks len 8){8 * blocks len 8 < max_size_t}
  -> lbytes len
let nat_to_text len input =
  let inputLen = blocks len 8 in
  let tmpLen = 8 * inputLen in
  let m = len % 8 in
  let ind = if m = 0 then 0 else 8 - m in

  let tmp = create tmpLen (u8 0) in
  let tmp = nat_to_text_ inputLen input tmpLen tmp in
  sub tmp ind (tmpLen - ind)
