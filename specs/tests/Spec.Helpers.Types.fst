module Spec.Helpers.Types

open Lib.IntTypes

type bytes = list uint8

type test_no = nat
type t_size = nat
type t_key = bytes
type t_len = bytes
type t_nonce = bytes
type t_aad = bytes
type t_tag = bytes
type t_input = bytes
type t_output = bytes

type test_type =
  | SHA3
  | AEAD

type test_suite =
  | SHA3_test of test_no * t_size * t_input * t_size * t_output
  | AEAD_test of test_no * t_key * t_nonce * t_input * t_output * t_aad * t_tag
