module Hacl.Ed25519



let sign signature secret msg len =
  Hacl.Impl.Ed25519.Sign.sign signature secret msg len

let verify public msg len signature =
  Hacl.Impl.Ed25519.Verify.verify public msg len signature

let secret_to_public out secret =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public out secret

let secret_to_public_expanded out secret_expanded =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public_expanded out secret_expanded

let point_add_compressed o p1 p2 = 
  push_frame();
  let buf1 = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let buf2 = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let buf3 = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let res1 = Hacl.Impl.Ed25519.PointDecompress.point_decompress buf1 p1 in
  let res2 = Hacl.Impl.Ed25519.PointDecompress.point_decompress buf2 p2 in
  let res = 
    if (res1 && res2) then (
      Hacl.Impl.Ed25519.PointAdd.point_add buf3 buf1 buf2;
      Hacl.Impl.Ed25519.PointCompress.point_compress o buf3;
      true
      )
    else false in
  pop_frame(); 
  res

let point_mul_compressed o scalar p = 
  push_frame();
  let buf1 = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let buf2 = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let res1 = Hacl.Impl.Ed25519.PointDecompress.point_decompress buf1 p in
  let res = if (res1) then (
      Hacl.Impl.Ed25519.Ladder.point_mul buf2 scalar buf1;
      Hacl.Impl.Ed25519.PointCompress.point_compress o buf2;
      true)
      else false in
  pop_frame();
  res


let sign_expanded signature secret msg len = 
  Hacl.Impl.Ed25519.Sign.sign_expanded signature secret msg len
