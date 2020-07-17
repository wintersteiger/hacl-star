module Hacl.Spec.Bignum

module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_add #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add a b

let bn_add_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add_lemma a b

let bn_sub #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub a b

let bn_sub_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a b

let bn_add_mod_n #len n a b =
  let c0, res0 = bn_add a b in
  let c1, res1 = bn_sub res0 n in
  let c = c0 -. c1 in
  map2 (mask_select c) res0 res1

let bn_add_mod_n_lemma #len n a b =
  let c0, res0 = bn_add a b in
  bn_add_lemma a b;
  let c1, res1 = bn_sub res0 n in
  bn_sub_lemma res0 n;
  assert (bn_v res1 - v c1 * pow2 (64 * len) == bn_v a + bn_v b - v c0 * pow2 (64 * len) - bn_v n);
  Math.Lemmas.distributivity_sub_left (v c0) (v c1) (pow2 (64 * len));
  assert (bn_v res1 + (v c0 - v c1) * pow2 (64 * len) == bn_v a + bn_v b - bn_v n);
  let c = c0 -. c1 in
  let res = map2 (mask_select c) res0 res1 in

  if bn_v a + bn_v b < bn_v n then begin
    assert (v c0 == 0);
    assert (v c1 == 1);
    assert (v c == pow2 64 - 1);
    bn_mask_select_lemma res0 res1 c;
    assert (bn_v res == bn_v res0);
    Math.Lemmas.small_mod (bn_v a + bn_v b) (bn_v n);
    assert (bn_v res == (bn_v a + bn_v b) % bn_v n) end
  else begin
    assert (bn_v a + bn_v b - bn_v n < bn_v n);
    bn_eval_bound res1 len;
    bn_eval_bound n len;
    assert (v c == 0);
    bn_mask_select_lemma res0 res1 c;
    assert (bn_v res == bn_v res1);
    Math.Lemmas.modulo_addition_lemma (bn_v a + bn_v b) (bn_v n) (- 1);
    assert (bn_v res % bn_v n == (bn_v a + bn_v b) % bn_v n);
    Math.Lemmas.small_mod (bn_v res) (bn_v n) end


let bn_mul #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul a b

let bn_mul_lemma #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul_lemma a b

let bn_sqr #aLen a =
  Hacl.Spec.Bignum.Multiplication.bn_sqr a

let bn_sqr_lemma #aLen a =
  Hacl.Spec.Bignum.Multiplication.bn_sqr_lemma a

let bn_mul1_lshift_add #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add a b j acc

let bn_mul1_lshift_add_lemma #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add_lemma a b j acc

let bn_rshift #len b i =
  slice b i len

let bn_rshift_lemma #len c i =
  calc (==) {
    bn_v c / pow2 (64 * i);
    (==) { bn_eval_split_i c i }
    (bn_v (slice c 0 i) + pow2 (64 * i) * bn_v (slice c i len)) / pow2 (64 * i);
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 i)) (pow2 (64 * i)) (bn_v (slice c i len)) }
    bn_v (slice c 0 i) / pow2 (64 * i) + bn_v (slice c i len);
    (==) { bn_eval_bound (slice c 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 i)) (pow2 (64 * i)) }
    bn_v (slice c i len);
  };
  assert (bn_v (slice c i len) == bn_v c / pow2 (64 * i))

let bn_sub_mask #len n a =
  let mask = BSeq.seq_eq_mask n a len in
  let mod_mask = map (logand mask) n in
  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  res

let bn_sub_mask_lemma #len n a =
  let mask = Lib.ByteSequence.seq_eq_mask n a len in
  assert (n == a ==> v mask == v (ones U64 SEC));
  assert (n =!= a ==> v mask == v (zeros U64 SEC));
  let mod_mask = map (logand mask) n in
  bn_mask_lemma n mask;
  assert (n == a ==> bn_v mod_mask == bn_v n);
  assert (n =!= a ==> bn_v mod_mask == 0);

  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a mod_mask;
  assert (bn_v res - v c * pow2 (64 * len) == bn_v a - bn_v mod_mask);
  bn_eval_bound res len;
  assert (bn_v res == bn_v a - bn_v mod_mask);

  Classical.move_requires_2 (bn_eval_inj len) n a

(* get and set i-th bit of a bignum *)

let bn_is_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  let tmp = (tmp >>. size j) &. u64 1 in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 tmp =^ 1uL)


#set-options "--z3rlimit 100"

let bn_is_bit_set_lemma #len b ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp1 = b.[i] >>. size j in
  let tmp2 = tmp1 &. u64 1 in
  mod_mask_lemma tmp1 1ul;
  assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1));
  assert (v tmp2 == v b.[i] / pow2 j % 2);

  calc (==) {
    v b.[i] / pow2 j % 2;
    (==) { bn_eval_index b i }
    (bn_v b / pow2 (64 * i) % pow2 64) / pow2 j % 2;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b / pow2 (64 * i)) j 64 }
    (bn_v b / pow2 (64 * i) / pow2 j) % pow2 (64 - j) % 2;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 (64 * i) / pow2 j) 1 (64 - j) }
    (bn_v b / pow2 (64 * i) / pow2 j) % 2;
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v b) (pow2 (64 * i)) (pow2 j) }
    (bn_v b / (pow2 (64 * i) * pow2 j)) % 2;
    (==) { Math.Lemmas.pow2_plus (64 * i) j }
    bn_v b / pow2 (64 * i + j) % 2;
    (==) { Math.Lemmas.euclidean_div_axiom ind 64 }
    bn_v b / pow2 ind % 2;
  };
  assert (v tmp2 == bn_v b / pow2 ind % 2)


let bn_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let inp = input.[i] <- input.[i] |. (u64 1 <<. size j) in
  inp


val bn_bit_set_lemma_aux: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a + b * pow2 c < pow2 (c + d) /\ a < pow2 c)
  (ensures  b < pow2 d)
let bn_bit_set_lemma_aux a b c d =
  Math.Lemmas.lemma_div_lt_nat (a + b * pow2 c) (c + d) c;
  assert ((a + b * pow2 c) / pow2 c < pow2 d);
  Math.Lemmas.lemma_div_plus a b (pow2 c);
  assert (a / pow2 c + b < pow2 d);
  Math.Lemmas.small_division_lemma_1 a (pow2 c)


val bn_lt_pow2_index_lemma: #len:size_nat -> b:lbignum len -> ind:size_nat{ind / 64 < len} -> Lemma
  (requires bn_v b < pow2 ind)
  (ensures (let i = ind / 64 in v b.[ind / 64] < pow2 (ind % 64) /\
    bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * v b.[i] /\
    bn_v (slice b (i + 1) len) = 0))

let bn_lt_pow2_index_lemma #len b ind =
  let i = ind / 64 in
  let j = ind % 64 in

  Math.Lemmas.euclidean_division_definition ind 64;
  assert (bn_v b < pow2 (i * 64 + j));
  Math.Lemmas.pow2_lt_compat (i * 64 + 64) (i * 64 + j);
  assert (bn_v b < pow2 (i * 64 + 64));

  bn_eval_split_i #len b (i + 1);
  //assert (bn_v b == bn_v (slice b 0 (i + 1)) + pow2 (64 * (i + 1)) * bn_v (slice b (i + 1) len));
  bn_eval_bound (slice b 0 (i + 1)) (i + 1);
  //assert (bn_v (slice b 0 (i + 1)) < pow2 (64 * i + 64));
  bn_bit_set_lemma_aux (bn_v (slice b 0 (i + 1))) (bn_v (slice b (i + 1) len)) (64 * (i + 1)) 0;
  assert (bn_v b == bn_v (slice b 0 (i + 1)));

  bn_eval_split_i #(i + 1) (slice b 0 (i + 1)) i;
  //assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * bn_v (slice b i (i + 1)));
  bn_eval1 (slice b i (i + 1));
  assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * v b.[i]);
  bn_eval_bound #i (slice b 0 i) i;
  bn_bit_set_lemma_aux (bn_v (slice b 0 i)) (v b.[i]) (i * 64) j;
  assert (v b.[i] < pow2 j)


let bn_bit_set_lemma #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  bn_lt_pow2_index_lemma #len input ind;
  assert (v input.[i] < pow2 j);

  let b = u64 1 <<. size j in
  let inp = input.[i] <- input.[i] |. b in
  FStar.Math.Lemmas.pow2_lt_compat 64 j;
  FStar.Math.Lemmas.modulo_lemma (pow2 j) (pow2 64);
  assert (v b == pow2 j);
  logor_disjoint (input.[i]) b j;
  assert (v inp.[i] == v input.[i] + v b);

  calc (==) {
    bn_v inp;
    (==) { bn_eval_split_i #len inp (i + 1);
    bn_eval_extensionality_j (slice inp (i + 1) len) (slice input (i + 1) len) (len - i - 1) }
    bn_v (slice inp 0 (i + 1));
    (==) { bn_eval_split_i #(i + 1) (slice inp 0 (i + 1)) i }
    bn_v (slice inp 0 i) + pow2 (i * 64) * bn_v (slice inp i (i + 1));
    (==) { bn_eval1 (slice inp i (i + 1)) }
    bn_v (slice inp 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { bn_eval_extensionality_j input inp i }
    bn_v (slice input 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { }
    bn_v (slice input 0 i) + pow2 (i * 64) * (v input.[i] + v b);
    (==) { Math.Lemmas.distributivity_add_right (pow2 (i * 64)) (v input.[i]) (v b) }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 (i * 64) * v b;
    (==) { Math.Lemmas.pow2_plus (i * 64) j; Math.Lemmas.euclidean_division_definition ind 64 }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 ind;
    (==) { }
    bn_v input + pow2 ind;
  }


(* Bignum comparison and test functions *)

let bn_is_zero #len b =
  let bn_zero = create len (u64 0) in
  let mask = Lib.ByteSequence.seq_eq_mask b bn_zero len in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB)

let bn_is_zero_lemma #len b =
  let bn_zero = create len (u64 0) in
  bn_eval_zeroes len len;
  let mask = Lib.ByteSequence.seq_eq_mask b bn_zero len in
  assert (b == bn_zero ==> v mask == v (ones U64 SEC));
  assert (b =!= bn_zero ==> v mask == v (zeros U64 SEC));
  Classical.move_requires_2 (bn_eval_inj len) b bn_zero;
  assert (bn_is_zero #len b == (if bn_v b = bn_v bn_zero then true else false))


let bn_is_odd #len b =
  if len > 0 then
    FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (b.[0] &. u64 1) =^ 1uL)
  else false

let bn_is_odd_lemma #len b =
  if len > 0 then begin
    bn_eval_split_i #len b 1;
    bn_eval1 (slice b 0 1);
    assert (bn_v b % 2 == (v b.[0] + pow2 64 * bn_v (slice b 1 len)) % 2);
    Math.Lemmas.pow2_plus 1 63;
    Math.Lemmas.modulo_addition_lemma (v b.[0]) 2 (pow2 63 * bn_v (slice b 1 len));
    assert (bn_v b % 2 == v b.[0] % 2);
    mod_mask_lemma b.[0] 1ul;
    assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1)) end
  else bn_eval0 #len b


val bn_mask_lt_f: #len:size_nat -> a:lbignum len -> b:lbignum len -> i:nat{i < len} -> acc:uint64 -> uint64
let bn_mask_lt_f #len a b i acc =
  let beq = eq_mask a.[i] b.[i] in
  let blt = lt_mask a.[i] b.[i] in
  mask_select beq acc (mask_select blt (ones U64 SEC) (zeros U64 SEC))

let bn_mask_lt_t (len:size_nat) (i:nat{i <= len}) = uint64

let bn_mask_lt #len a b =
  Loops.repeat_gen len (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0)

// val bn_mask_lt_aux: len:size_nat -> a:lbignum len -> b:lbignum len -> k:pos{k <= len} -> Lemma
//   (requires v a.[k - 1] <> v b.[k - 1])
//   (ensures (if v a.[k - 1] < v b.[k - 1] then eval_ len a k < eval_ len b k else eval_ len a k > eval_ len b k))
// let bn_mask_lt_aux len a b k =
//   if v a.[k - 1] < v b.[k - 1] then bn_eval_lt len a b k else bn_eval_lt len b a k

val bn_mask_lt_lemma_step:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:pos{k <= len} -> mask0:uint64 -> Lemma
  (requires
    (if v mask0 = 0 then eval_ len a (k - 1) >= eval_ len b (k - 1) else eval_ len a (k - 1) < eval_ len b (k - 1)) /\
    (v mask0 == 0 \/ v mask0 == v (ones U64 SEC)))
  (ensures (let mask = bn_mask_lt_f #len a b (k - 1) mask0 in
    (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k) /\
    (v mask == 0 \/ v mask == v (ones U64 SEC))))

let bn_mask_lt_lemma_step #len a b k mask0 =
  let mask = bn_mask_lt_f #len a b (k - 1) mask0 in
  let ai = a.[k - 1] in
  let bi = b.[k - 1] in
  let beq = eq_mask ai bi in
  assert (if v ai = v bi then v beq == v (ones U64 SEC) else v beq == 0);
  let blt = lt_mask ai bi in
  assert (if v ai < v bi then v blt == v (ones U64 SEC) else v blt == 0);

  let res0 = mask_select blt (ones U64 SEC) (zeros U64 SEC) in
  let mask = mask_select beq mask0 res0 in
  //assert (mask == bn_mask_lt_f #len a b (k - 1) mask0);

  mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
  mask_select_lemma beq mask0 res0;

  if v beq = 0 then begin
    assert (v mask = v res0);
    mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
    //assert (v res0 == (if v blt = 0 then 0 else v (ones U64 SEC)));
    assert (if v mask = 0 then v ai > v bi else v ai < v bi);
    if v a.[k - 1] < v b.[k - 1] then bn_eval_lt len a b k else bn_eval_lt len b a k;
    () end
  else begin
    assert (v mask = v mask0);
    //assert (v beq == v (ones U64 SEC));
    //assert (if v mask = v mask0 then v ai = v bi else v ai <> v bi);
    assert (v ai == v bi);
    bn_eval_unfold_i a k;
    bn_eval_unfold_i b k;
    () end


val bn_mask_lt_lemma_loop:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:nat{k <= len} -> Lemma
  (let mask = Loops.repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
   (v mask == 0 \/ v mask == v (ones U64 SEC)) /\
   (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k))

let rec bn_mask_lt_lemma_loop #len a b k =
  let mask = Loops.repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
  if k = 0 then begin
    Loops.eq_repeat_gen0 k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0);
    assert (v mask = 0);
    bn_eval0 a;
    bn_eval0 b end
  else begin
    let mask0 = Loops.repeat_gen (k - 1) (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
    Loops.unfold_repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) (k - 1);
    bn_mask_lt_lemma_loop #len a b (k - 1);
    bn_mask_lt_lemma_step #len a b k mask0 end

let bn_mask_lt_lemma #len a b =
  bn_mask_lt_lemma_loop #len a b len


let bn_is_less #len a b =
  let mask = bn_mask_lt a b in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB)

let bn_is_less_lemma #len a b =
  bn_mask_lt_lemma #len a b

// we could compare bBits with x, but we don't have the bn_num_bits function
// bn_v b < pow2 x
let bn_lt_pow2 #len b x =
  if x >= 64 * len then true
  else begin
    let b2 = create len (u64 0) in
    let b2 = bn_bit_set b2 x in
    bn_is_less b b2 end

let bn_lt_pow2_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  if x >= 64 * len then
    Math.Lemmas.pow2_le_compat x (64 * len)
  else begin
    let b2 = create len (u64 0) in
    bn_eval_zeroes len len;
    assert (bn_v b2 = 0);
    //assert (bn_v b2 < pow2 x);
    let b2' = bn_bit_set b2 x in
    bn_bit_set_lemma b2 x;
    assert (bn_v b2' == pow2 x);
    bn_is_less_lemma b b2' end

//pow2 x < bn_v b
let bn_gt_pow2 #len b x =
  if x >= 64 * len then false
  else begin
    let b2 = create len (u64 0) in
    let b2 = bn_bit_set b2 x in
    bn_is_less b2 b end

let bn_gt_pow2_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  if x >= 64 * len then
    Math.Lemmas.pow2_le_compat x (64 * len)
  else begin
    let b2 = create len (u64 0) in
    bn_eval_zeroes len len;
    assert (bn_v b2 = 0);
    //assert (bn_v b2 < pow2 x);
    let b2' = bn_bit_set b2 x in
    bn_bit_set_lemma b2 x;
    assert (bn_v b2' == pow2 x);
    bn_is_less_lemma b2' b end

(* Conversion functions *)

let bn_from_uint len x =
  let b = create len (u64 0) in
  b.[0] <- x

let bn_from_uint_lemma len x =
  let b = create len (u64 0) in
  let b = b.[0] <- x in
  bn_eval_split_i b 1;
  assert (bn_v b == bn_v (slice b 0 1) + pow2 64 * bn_v (slice b 1 len));
  eq_intro (slice b 1 len) (create (len - 1) (u64 0));
  bn_eval_zeroes (len - 1) (len - 1);
  assert (bn_v b == bn_v (slice b 0 1));
  bn_eval1 (slice b 0 1)

let bn_from_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be len b

let bn_from_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma len b

let bn_from_bytes_le len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le len b

let bn_from_bytes_le_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma len b

let bn_to_bytes_be len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be len b

let bn_to_bytes_be_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma len b

let bn_to_bytes_le len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le len b

let bn_to_bytes_le_lemma len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le_lemma len b