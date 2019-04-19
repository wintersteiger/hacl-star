open Spec_Helpers_Types

let to_bytes (bs: string): bytes =
  let rec split_into_bytes s =
    if BatString.is_empty s then
      []
    else begin
      (BatString.sub s 0 2)::(split_into_bytes (BatString.sub s 2 (BatString.length s - 2))) end
  in
  assert (BatString.length bs mod 2 = 0);
  BatList.map (fun byte -> FStar_UInt8.uint_to_t (Prims.parse_int (BatString.concat "" ["0x"; byte]))) (split_into_bytes bs)

let parse_test_vectors (path: string) (typ: test_type): test_suite list =
  let parse_vector typ (v: Yojson.Safe.json) =
    match v with
    | `Assoc fields -> begin
      match (typ, fields) with
      | (AEAD, [("test_no", `Int test_no); ("key", `String key); ("nonce", `String nonce);  ("input", `String input);
                ("output", `String output); ("aad", `String aad); ("tag", `String tag); ]) ->
        AEAD_test (Z.of_int test_no, to_bytes key, to_bytes nonce, to_bytes input, to_bytes output, to_bytes aad, to_bytes tag)
      | (SHA3, [("test_no", `Int test_no); ("input_len", `Int input_len); ("input", `String input); ("output_len", `Int output_len); ("output", `String output)]) ->
        SHA3_test (Z.of_int test_no, Z.of_int input_len, to_bytes input, Z.of_int output_len, to_bytes output)
      | _ -> failwith "Incorrect test vector format: %s\n" path
    end
    | _ -> failwith "Incorrect test vector format: %s\n" path
  in
  let json = Yojson.Safe.from_channel (open_in path) in
  match json with
  | `List test_vectors -> List.map (parse_vector typ) test_vectors
  | _ -> failwith "Incorrect test vector format: %s\n" path

let get_test_suite (typ: test_type): (test_suite list) option =
  let tests =  match typ with
    | SHA3 -> parse_test_vectors "../tests/generated/json/fips-202-sha3_test.json" SHA3
    | AEAD -> parse_test_vectors "../tests/generated/json/google-wycheproof-chacha20_poly1305_test.json" AEAD
  in
  if BatList.is_empty tests then None else Some tests
