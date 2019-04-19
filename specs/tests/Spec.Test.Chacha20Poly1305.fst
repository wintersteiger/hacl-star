module Spec.Test.Chacha20Poly1305

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
module H =  Spec.Helpers.Types
module CP = Spec.Chacha20Poly1305

let test_chacha20poly1305
  (test_no: nat)
  (key: CP.key)
  (iv: CP.nonce)
  (pt: bytes{length pt + CP.size_block <= max_size_t})
  (aad: bytes{length aad <= max_size_t /\ (length pt + length aad) / Spec.Chacha20.blocklen <= max_size_t})
  (ct: bytes{length ct + CP.size_block <= max_size_t})
  (tag: CP.tag) =
  let msg_len = length pt in
  let tag_len = length tag in
  let test_encrypt = CP.aead_encrypt key iv pt aad in
  let test_ct = sub test_encrypt 0 msg_len in
  let test_tag = sub test_encrypt msg_len tag_len in
  let test_decrypt = CP.aead_decrypt key iv test_ct test_tag aad in

  let result_encryption = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_ct ct in
  let result_mac = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_tag tag in
  let dec_p = match test_decrypt with | Some p -> p | None -> create msg_len (u8 0) in
  let result_decryption = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) dec_p pt in
  if result_encryption && result_mac && result_decryption then begin
    IO.print_string "Test "; IO.print_string (UInt32.to_string (nat_to_uint test_no)); IO.print_string ": success\n" end
  else begin
    IO.print_string "Test "; IO.print_string (UInt32.to_string (nat_to_uint test_no)); IO.print_string " failed: ";
    if not result_encryption then begin
      IO.print_string "encryption "// ;
      // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test_ct); IO.print_string "\n";
      // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list ct);  IO.print_string "\n"
    end;
    if not result_mac then begin
      IO.print_string "MAC "// ;
      // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list test_tag); IO.print_string "\n";
      // List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a))) (to_list tag);  IO.print_string "\n"
    end;
    if not result_decryption then
      IO.print_string "decryption ";
    IO.print_string "\n"
  end

let test () =
  let test_vectors = Spec.Helpers.get_test_suite H.AEAD in
  let results = match test_vectors with
  | Some ts ->
      List.map (fun t -> match t with | H.AEAD_test (test_no, key, iv, pt, aad, ct, tag) ->
        test_chacha20poly1305 test_no (of_list key) (of_list iv) (of_list pt) (of_list ct) (of_list aad) (of_list tag) | _ -> ()) ts
  | _ -> []
  in
  true

