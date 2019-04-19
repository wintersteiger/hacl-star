module Spec.Test.SHA3

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
module H =  Spec.Helpers.Types

let print_and_compare (len:size_nat) (test_expected:lbytes len) (test_result: option (lbytes len)) (test_no: nat) =
  match test_result with
  | Some result ->
    let test_success = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_expected result in
    // if test_success then begin
    //   IO.print_string "\nTest succeeded: ";
    //   IO.print_string (UInt32.to_string (nat_to_uint #U32 #PUB test_no))
    // end else begin
    if not test_success then begin
      IO.print_string "\nTest failed: ";
      IO.print_string (UInt32.to_string (nat_to_uint #U32 #PUB test_no));
      IO.print_string "\nResult:   ";
      List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list result);
      IO.print_string "\nExpected: ";
      List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test_expected)
    end
  | None ->
    IO.print_string "\nMalformed test: ";
    IO.print_string (UInt32.to_string (nat_to_uint #U32 #PUB test_no))

let test_sha3 (msg_len: size_nat) (output_len: size_nat) (test_no: nat) (msg:lbytes msg_len) (expected: lbytes output_len) =
  let test = match output_len with
    | 28 -> Some (Spec.SHA3.sha3_224 msg_len msg)
    | 32 -> Some (Spec.SHA3.sha3_256 msg_len msg)
    | 48 -> Some (Spec.SHA3.sha3_384 msg_len msg)
    | 64 -> Some (Spec.SHA3.sha3_512 msg_len msg)
    | _ -> None
  in
  print_and_compare output_len expected test test_no

let test () =
  let test_suite = Spec.Helpers.get_test_suite H.SHA3 in
  let results = match test_suite with
  | Some ts ->
      List.map (fun t -> match t with | H.SHA3_test (test_no, pt_len, pt, md_len, md) ->
        test_sha3 pt_len (md_len / 8) test_no (of_list pt) (of_list md) | _ -> ()) ts
  | _ -> []
  in
  true
