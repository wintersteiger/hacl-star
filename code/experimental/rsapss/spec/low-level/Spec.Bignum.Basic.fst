module Spec.Bignum.Basic

open FStar.Mul

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence

open Spec.Bignum.Base
open Spec.Convert

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val eq_u64:a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b = FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

val lt_u64:a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

let lbignum len = lseq uint64 len

val bval:len:size_pos -> b:lbignum len -> i:size_nat -> Tot uint64
let bval len b i = if i < len then b.[i] else u64 0

val eval_i:
    len:size_nat
  -> s:lbignum len
  -> i:size_nat{i <= len}
  -> Tot (res:nat{res < x_i i}) (decreases i)
let rec eval_i len s i =
  if i = 0 then 0
  else begin
    let res = eval_i len s (i - 1) + uint_to_nat s.[i - 1] * x_i (i - 1) in
    assert (res <= x_i (i - 1) + (pow2 64 - 1) * x_i (i - 1));
    assert (res <= x_i (i - 1) + pow2 64 * x_i (i - 1) - x_i (i - 1));
    FStar.Math.Lemmas.pow2_plus 64 (64 * (i - 1));
    res end

let eval (len:size_nat) s = eval_i len s len

noeq type bignum (nBits:size_nat) =
  | Bignum:len:size_pos{blocks nBits 64 <= len}
        -> bn:lbignum len{eval_i len bn (blocks nBits 64) == eval len bn /\
	                 (forall (i:size_nat{blocks nBits 64 <= i /\ i < len}). uint_v bn.[i] = 0) /\ eval len bn < pow2 nBits}
        -> bignum nBits

#set-options "--max_fuel 2"

val lemma_eval_incr:
     len:size_pos
  -> s:lbignum len
  -> i:size_nat{0 < i /\ i <= len}
  -> Lemma
    (requires True)
    (ensures eval_i len s i == eval_i len s (i - 1) + uint_to_nat s.[i - 1] * x_i (i - 1))
let lemma_eval_incr len s i = ()

val lemma_eval_init_seq_is_0:
     len:size_pos
  -> s:lbignum len
  -> i:size_nat{i <= len}
  -> Lemma
    (requires (forall (j:size_nat). j < len ==> uint_to_nat s.[j] = 0))
    (ensures eval_i len s i = 0)
let rec lemma_eval_init_seq_is_0 len s i =
  if i = 0 then ()
  else lemma_eval_init_seq_is_0 len s (i - 1)

val lemma_eval_u64:
     len:size_pos
  -> s:lbignum len
  -> v_u64:uint64
  -> i:size_nat{0 < i /\ i <= len}
  -> Lemma
    (requires
      uint_to_nat s.[0] = uint_v v_u64 /\
      (forall (j:size_nat). 0 < j /\ j < len ==> uint_to_nat s.[j] = 0))
    (ensures
      eval_i len s i = uint_v v_u64)
let rec lemma_eval_u64 len s v_u64 i =
  if i = 1 then ()
  else lemma_eval_u64 len s v_u64 (i - 1)

val lemma_eval_equal1:
     len1:size_nat
  -> s1:lbignum len1
  -> len2:size_nat{len2 <= len1}
  -> s2:lbignum len2
  -> i:size_nat{i <= len2}
  -> Lemma
    (requires
      (forall (j:size_nat{j < i}). uint_v s1.[j] == uint_v s2.[j]))
    (ensures
      eval_i len1 s1 i == eval_i len2 s2 i)
let rec lemma_eval_equal1 len1 s1 len2 s2 i =
  if i = 0 then ()
  else lemma_eval_equal1 len1 s1 len2 s2 (i - 1)

val lemma_eval_equal2:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> i:size_nat{bLen <= i /\ i <= aLen}
  -> Lemma
    (requires
      (forall (j:size_nat{j < bLen}). uint_v a.[j] = uint_v b.[j]) /\
      (forall (j:size_nat{bLen <= j /\ j < aLen}). uint_v a.[j] = 0))
    (ensures
      eval_i aLen a i = eval bLen b)
let rec lemma_eval_equal2 aLen a bLen b i =
  if i = bLen then lemma_eval_equal1 aLen a bLen b i
  else lemma_eval_equal2 aLen a bLen b (i - 1)

val lemma_eval_pow2:
     len:size_pos
  -> len0:size_pos{len0 <= len}
  -> b:lbignum len
  -> i:size_nat{len0 <= i /\ i <= len}
  -> Lemma
    (requires eval len b < x_i len0)
    (ensures
      eval len b == eval_i len b i /\
      (forall (j:size_nat{i <= j /\ j < len}). uint_v b.[j] = 0))
let lemma_eval_pow2 len len0 b i = admit()

val eval_is_greater_len:
    len:size_pos
  -> b:lbignum len
  -> i:size_nat
  -> nat
let rec eval_is_greater_len len b i =
  if i <= len then eval_i len b i
  else eval_is_greater_len len b (i - 1)

val lemma_eval_is_greater_len:
    len:size_pos
  -> b:lbignum len
  -> i:size_nat{i >= len}
  -> Lemma (eval len b == eval_is_greater_len len b i)
let rec lemma_eval_is_greater_len len b i =
  if i = len then ()
  else lemma_eval_is_greater_len len b (i - 1)

val lemma_mult_x1_xi:
  i:size_nat{i + 1 < max_size_t}
  -> Lemma (x_i 1 * x_i i = x_i (i + 1))
let lemma_mult_x1_xi i =
  FStar.Math.Lemmas.pow2_plus (64 * 1) (64 * i)

let bn_v #nBits b = eval b.len b.bn

let bn_const_1 #bits =
  let len = blocks bits 64 in
  let r = create len (u64 0) in
  let r = r.[0] <- u64 1 in
  lemma_eval_u64 len r (u64 1) len;
  assert (eval len r == 1);
  assert_norm (1 < pow2 bits);
  let res:bignum bits = Bignum len r in
  res

let bn_const_0 #bits =
  let len = blocks bits 64 in
  let r = create len (u64 0) in
  lemma_eval_u64 len r (u64 0) len;
  assert (eval len r == 0);
  assert_norm (0 < pow2 bits);
  let res:bignum bits = Bignum len r in
  res

let bn_cast_le #bits mBits b =
  let mLen = blocks mBits 64 in
  FStar.Math.Lemmas.pow2_le_compat (64 * mLen) mBits;
  lemma_eval_pow2 b.len mLen b.bn mLen;
  let r = sub b.bn 0 mLen in
  lemma_eval_equal2 b.len b.bn mLen r b.len;
  let res:bignum mBits = Bignum mLen r in
  res

let bn_cast_gt #bits mBits b =
  let nLen = blocks bits 64 in
  assert (nLen <= b.len);
  let b_bn = sub b.bn 0 nLen in
  lemma_eval_equal2 b.len b.bn nLen b_bn b.len;
  let mLen = blocks mBits 64 in
  let r = create mLen (u64 0) in
  let r = update_sub r 0 nLen b_bn in
  lemma_eval_equal2 mLen r nLen b_bn mLen;
  assert (eval mLen r < pow2 mBits);
  let res:bignum mBits = Bignum mLen r in
  res

val bn_add_f_pred:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> i:size_nat{i <= aLen}
  -> tuple2 carry (lbignum aLen)
  -> Type0
let bn_add_f_pred aLen a bLen b i (c, res) =
  eval_i aLen res i + uint_v c * x_i i == eval_i aLen a i + eval_is_greater_len bLen b i

#set-options "--z3rlimit 100"

val bn_add_f:
    aLen:size_pos{aLen + 1 < max_size_t}
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> repeatable #(tuple2 carry (lbignum aLen)) #aLen (bn_add_f_pred aLen a bLen b)
let bn_add_f aLen a bLen b i (c, res) =
  assert (bn_add_f_pred aLen a bLen b i (c, res));
  let bi = bval bLen b i in
  let c', res_i = addcarry_u64 a.[i] bi c in
  assert (uint_v res_i + uint_v c' * x_i 1 == uint_v a.[i] + uint_v bi + uint_v c);
  let res' = res.[i] <- res_i in
  lemma_eval_equal1 aLen res aLen res' i;
  assert (eval_i aLen res i == eval_i aLen res' i);
  lemma_eval_incr aLen res' (i + 1);
  assert (eval_i aLen res' (i + 1) == eval_i aLen res' i + uint_v res'.[i] * x_i i); //from eval_i
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i + eval_is_greater_len bLen b i - uint_v c * x_i i + (uint_v a.[i] + uint_v bi + uint_v c - uint_v c' * x_i 1) * x_i i); //expansion
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i + eval_is_greater_len bLen b i - uint_v c * x_i i + uint_v a.[i] * x_i i + uint_v bi * x_i i + uint_v c * x_i i - uint_v c' * x_i 1 * x_i i);
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i + eval_is_greater_len bLen b i + uint_v a.[i] * x_i i + uint_v bi * x_i i - uint_v c' * x_i 1 * x_i i);
  lemma_mult_x1_xi i;
  assert (eval_i aLen res' (i + 1) + uint_v c' * x_i (i + 1) == eval_i aLen a i + eval_is_greater_len bLen b i + uint_v a.[i] * x_i i + uint_v bi * x_i i);
  assert (eval_i aLen res' (i + 1) + uint_v c' * x_i (i + 1) == eval_i aLen a (i+1) + eval_is_greater_len bLen b (i+1));
  c', res'

#set-options "--z3rlimit 30"

val bn_add_:
    aLen:size_pos{aLen + 1 < max_size_t}
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> Pure (tuple2 carry (lbignum aLen))
    (requires True)
    (ensures  fun (c', res') -> eval aLen res' + uint_v c' * x_i aLen = eval aLen a + eval bLen b)
let bn_add_ aLen a bLen b =
  let res = create aLen (u64 0) in
  let c', res' =
    repeati_inductive aLen
    (bn_add_f_pred aLen a bLen b)
    (fun i (c, res) ->
      bn_add_f aLen a bLen b i (c, res)
    ) (u8 0, res) in
  assert (eval_i aLen res' aLen + uint_v c' * x_i aLen == eval_i aLen a aLen + eval_is_greater_len bLen b aLen);
  lemma_eval_is_greater_len bLen b aLen;
  c', res'

let bn_add #nBits #mBits a b =
  let aLen = blocks nBits 64 in
  assert (nBits <= 64 * aLen);
  let a_bn = sub a.bn 0 aLen in
  lemma_eval_equal2 a.len a.bn aLen a_bn a.len;
  let bLen = blocks mBits 64 in
  let b_bn = sub b.bn 0 bLen in
  lemma_eval_equal2 b.len b.bn bLen b_bn b.len;
  assert (bLen <= aLen);
  let (c', r) = bn_add_ aLen a_bn bLen b_bn in
  assert (eval aLen r + uint_v c' * x_i aLen == eval aLen a_bn + eval bLen b_bn);
  assert (eval aLen a_bn + eval bLen b_bn < pow2 nBits);
  assert (eval aLen r + uint_v c' * x_i aLen < pow2 nBits);
  FStar.Math.Lemmas.pow2_le_compat (64*aLen) nBits;
  assert (uint_v c' = 0);
  let res:bignum nBits = Bignum aLen r in
  res

#set-options "--max_fuel 0"

val lemma_bn_add:
    #n:size_pos
  -> #m:size_pos{n >= m}
  -> a:bignum n
  -> b:bignum m
  -> Lemma (bn_v a + bn_v b < pow2 (n + 1))
let lemma_bn_add #n #m a b =
  FStar.Math.Lemmas.pow2_le_compat n m;
  assert (bn_v a + bn_v b < pow2 n + pow2 n);
  FStar.Math.Lemmas.pow2_double_sum n

let bn_add_carry #nBits #mBits a b =
  let aLen = blocks nBits 64 in
  assert (nBits <= 64 * aLen);
  let a_bn = sub a.bn 0 aLen in
  lemma_eval_equal2 a.len a.bn aLen a_bn a.len;
  let bLen = blocks mBits 64 in
  let b_bn = sub b.bn 0 bLen in
  lemma_eval_equal2 b.len b.bn bLen b_bn b.len;
  assert (bLen <= aLen);
  let c', r = bn_add_ aLen a_bn bLen b_bn in
  assert (eval aLen r + uint_v c' * x_i aLen == eval aLen a_bn + eval bLen b_bn);
  lemma_bn_add #nBits #mBits a b;
  assert (eval aLen r + uint_v c' * x_i aLen < pow2 (nBits + 1));
  assert (eval aLen r < pow2 (64 * aLen));
  let resLen = blocks (nBits + 1) 64 in
  assert (nBits + 1 <= resLen * 64);
  assert (aLen <= resLen);
  let r1 = create resLen (u64 0) in
  let r1 = update_sub r1 0 aLen r in
  lemma_eval_equal2 resLen r1 aLen r aLen;
  if aLen < resLen then begin
    let r2 = r1.[aLen] <- to_u64 c' in
    lemma_eval_equal1 resLen r2 resLen r1 aLen;
    lemma_eval_incr resLen r2 resLen;
    assert (eval resLen r2 == eval_i resLen r2 aLen + uint_v r2.[aLen] * x_i aLen);
    assert (eval resLen r2 < pow2 (nBits + 1));
    let res:bignum (nBits + 1) = Bignum resLen r2 in
    res end
  else begin
    FStar.Math.Lemmas.pow2_le_compat (64*resLen) (nBits+1);
    assert (uint_v c' = 0);
    let res:bignum (nBits+1) = Bignum resLen r1 in
    res end

val bn_sub_f_pred:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> i:size_nat{i <= aLen}
  -> tuple2 carry (lbignum aLen)
  -> Type0
let bn_sub_f_pred aLen a bLen b i (c, res) =
  eval_i aLen res i - uint_v c * x_i i == eval_i aLen a i - eval_is_greater_len bLen b i

#set-options "--z3rlimit 100 --max_fuel 2"

val bn_sub_f:
    aLen:size_pos{aLen + 1 < max_size_t}
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> repeatable #(tuple2 carry (lbignum aLen)) #aLen (bn_sub_f_pred aLen a bLen b)
let bn_sub_f aLen a bLen b i (c, res) =
  assert (bn_sub_f_pred aLen a bLen b i (c, res));
  let bi = bval bLen b i in
  let c', res_i = subborrow_u64 a.[i] bi c in
  assert (uint_v res_i - uint_v c' * x_i 1 == uint_v a.[i] - uint_v bi - uint_v c);
  let res' = res.[i] <- res_i in
  lemma_eval_equal1 aLen res aLen res' i;
  assert (eval_i aLen res i == eval_i aLen res' i);
  lemma_eval_incr aLen res' (i + 1);
  assert (eval_i aLen res' (i + 1) == eval_i aLen res' i + uint_v res'.[i] * x_i i); //from eval_i
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i - eval_is_greater_len bLen b i + uint_v c * x_i i + (uint_v a.[i] - uint_v bi - uint_v c + uint_v c' * x_i 1) * x_i i); //expansion
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i - eval_is_greater_len bLen b i + uint_v c * x_i i + uint_v a.[i] * x_i i - uint_v bi * x_i i - uint_v c * x_i i + uint_v c' * x_i 1 * x_i i);
  assert (eval_i aLen res' (i + 1) == eval_i aLen a i - eval_is_greater_len bLen b i + uint_v a.[i] * x_i i - uint_v bi * x_i i + uint_v c' * x_i 1 * x_i i);
  lemma_mult_x1_xi i;
  assert (eval_i aLen res' (i + 1) - uint_v c' * x_i (i + 1) == eval_i aLen a i - eval_is_greater_len bLen b i + uint_v a.[i] * x_i i - uint_v bi * x_i i);
  assert (eval_i aLen res' (i + 1) - uint_v c' * x_i (i + 1) == eval_i aLen a (i+1) - eval_is_greater_len bLen b (i+1));
  c', res'

val bn_sub_:
    aLen:size_pos{aLen + 1 < max_size_t}
  -> a:lbignum aLen
  -> bLen:size_pos{bLen <= aLen}
  -> b:lbignum bLen
  -> Pure (tuple2 carry (lbignum aLen))
    (requires True)
    (ensures  fun (c', res') -> eval aLen res' - uint_v c' * x_i aLen = eval aLen a - eval bLen b)
let bn_sub_ aLen a bLen b =
  let res = create aLen (u64 0) in
  let c', res' =
    repeati_inductive aLen
    (bn_sub_f_pred aLen a bLen b)
    (fun i (c, res) ->
      bn_sub_f aLen a bLen b i (c, res)
    ) (u8 0, res) in
  assert (eval_i aLen res' aLen - uint_v c' * x_i aLen == eval_i aLen a aLen - eval_is_greater_len bLen b aLen);
  lemma_eval_is_greater_len bLen b aLen;
  c', res'

#set-options "--z3rlimit 30 --max_fuel 0"

let bn_sub #nBits #mBits a b =
  let aLen = blocks nBits 64 in
  assert (nBits <= 64 * aLen);
  let a_bn = sub a.bn 0 aLen in
  lemma_eval_equal2 a.len a.bn aLen a_bn a.len;
  let bLen = blocks mBits 64 in
  let b_bn = sub b.bn 0 bLen in
  lemma_eval_equal2 b.len b.bn bLen b_bn b.len;
  assume (bLen <= aLen); ///FIX
  let (c', r) = bn_sub_ aLen a_bn bLen b_bn in
  assert (eval aLen r - uint_v c' * x_i aLen == eval aLen a_bn - eval bLen b_bn);
  assert (eval aLen r - uint_v c' * x_i aLen < pow2 nBits);
  assert (0 <= eval aLen a_bn - eval bLen b_bn);
  assert (0 <= eval aLen r - uint_v c' * x_i aLen);
  assert (eval aLen r < pow2 (64*aLen));
  assert (uint_v c' = 0);
  let res:bignum nBits = Bignum aLen r in
  res

val bn_mul_f_pred:
  aLen:size_pos
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_nat
  -> resLen:size_nat{aLen + j < resLen}
  -> res:lbignum resLen
  -> i:size_nat{i <= aLen}
  -> tuple2 uint64 (lbignum resLen)
  -> Type0
let bn_mul_f_pred aLen a l j resLen res i (c', res') =
  eval_i resLen res' (i + j) + uint_v c' * x_i (i + j) == eval_i resLen res (i + j) + eval_i aLen a i * uint_v l * x_i j /\
  (forall (k:size_nat{i + j <= k /\ k < resLen}). uint_v res'.[k] = uint_v res.[k])

val lemma_mult_xi_xj:
    i:size_nat
  -> j:size_nat{i + j < max_size_t}
  -> Lemma (x_i i * x_i j = x_i (i + j))
let lemma_mult_xi_xj i j =
  FStar.Math.Lemmas.pow2_plus (64 * i) (64 * j)

val lemma_mult_abcd:a:nat -> b:nat -> c:nat -> d:nat
  -> Lemma (a * b * c * d = (a * c) * (b * d))
let lemma_mult_abcd a b c d = ()

val bn_mul_f:
    aLen:size_pos
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_nat
  -> resLen:size_nat{aLen + j < resLen /\ resLen + 1 < max_size_t}
  -> res:lbignum resLen
  -> repeatable #(tuple2 uint64 (lbignum resLen)) #aLen (bn_mul_f_pred aLen a l j resLen res)
let bn_mul_f aLen a l j resLen res i (c1, res1) = admit();
  assert (eval_i resLen res1 (i+j) + uint_v c1 * x_i (i+j) == eval_i resLen res (i+j) + eval_i aLen a i * uint_v l * x_i j /\ uint_v res1.[i+j] = uint_v res.[i+j]);
  let c2, res_ij = mul_carry_add_u64 a.[i] l c1 res1.[i+j] in
  assert (uint_v res_ij + uint_v c2 * x_i 1 == uint_v a.[i] * uint_v l + uint_v c1 + uint_v res1.[i+j]);
  let res2 = res1.[i+j] <- res_ij in
  lemma_eval_equal1 resLen res2 resLen res1 (i+j);
  assert (eval_i resLen res2 (i+j) == eval_i resLen res1 (i+j));
  lemma_eval_incr resLen res2 (i+j+1);
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res2 (i+j) + uint_v res2.[i+j] * x_i (i+j)); //from eval_i
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res (i+j) + eval_i aLen a i * uint_v l * x_i j - uint_v c1 * x_i (i+j) + uint_v res2.[i+j] * x_i (i+j));
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res (i+j) + eval_i aLen a i * uint_v l * x_i j - uint_v c1 * x_i (i+j) +
	 (uint_v a.[i] * uint_v l + uint_v c1 + uint_v res1.[i+j] - uint_v c2 * x_i 1) * x_i (i+j));
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res (i+j) + eval_i aLen a i * uint_v l * x_i j - uint_v c1 * x_i (i+j) +
	 uint_v a.[i] * uint_v l * x_i (i+j) + uint_v c1 * x_i (i+j) + uint_v res1.[i+j] * x_i (i+j) - uint_v c2 * x_i 1 * x_i (i+j));
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res (i+j) + eval_i aLen a i * uint_v l * x_i j +
	 uint_v a.[i] * uint_v l * x_i (i+j) + uint_v res1.[i+j] * x_i (i+j) - uint_v c2 * x_i 1 * x_i (i+j));
  lemma_eval_incr resLen res (i+j+1);
  assert (eval_i resLen res2 (i+j+1) == eval_i resLen res (i+j+1) + eval_i aLen a i * uint_v l * x_i j + uint_v a.[i] * uint_v l * x_i (i+j) - uint_v c2 * x_i 1 * x_i (i+j));
  assert (i+j+1 < max_size_t);
  lemma_mult_x1_xi (i+j);
  //assert (eval_i resLen res2 (i+j+1) + uint_v c2 * x_i (i+j+1) == eval_i resLen res (i+j+1) + eval_i aLen a i * uint_v l * x_i j + uint_v a.[i] * uint_v l * x_i (i+j));
  lemma_mult_xi_xj i j;
  //assert (eval_i resLen res2 (i+j+1) + uint_v c2 * x_i (i+j+1) == eval_i resLen res (i+j+1) + eval_i aLen a i * uint_v l * x_i j + uint_v a.[i] * uint_v l * x_i i * x_i j);
  lemma_mult_abcd (uint_v a.[i]) (uint_v l) (x_i i) (x_i j);
  //assert (eval_i resLen res2 (i+j+1) + uint_v c2 * x_i (i+j+1) == eval_i resLen res (i+j+1) + eval_i aLen a i * uint_v l * x_i j + (uint_v a.[i] * x_i i) * (uint_v l * x_i j));
  FStar.Math.Lemmas.paren_mul_right (eval_i aLen a i) (uint_v l) (x_i j);
  FStar.Math.Lemmas.distributivity_add_left (eval_i aLen a i) (uint_v a.[i] * x_i i) (uint_v l * x_i j);
  //assert (eval_i resLen res2 (i+j+1) + uint_v c2 * x_i (i+j+1) == eval_i resLen res (i+j+1) + (eval_i aLen a i + uint_v a.[i] * x_i i) * uint_v l * x_i j);
  lemma_eval_incr aLen a (i+1);
  //assert (eval_i resLen res2 (i+j+1) + uint_v c2 * x_i (i+j+1) == eval_i resLen res (i+j+1) + eval_i aLen a (i+1) * uint_v l * x_i j);
  c2, res2

val bn_mul_by_limb_addj:
    aLen:size_pos
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_nat
  -> resLen:size_pos{aLen + j < resLen /\ resLen + 1 < max_size_t}
  -> res:lbignum resLen
  -> Pure (tuple2 uint64 (lbignum resLen))
    (requires True)
    (ensures  fun (c', res') ->
      eval_i resLen res' (aLen + j) + uint_v c' * x_i (aLen + j) ==
      eval_i resLen res (aLen + j) + eval aLen a * uint_v l * x_i j)
let bn_mul_by_limb_addj aLen a l j resLen res =
  let c', res' =
    repeati_inductive aLen
    (bn_mul_f_pred aLen a l j resLen res)
    (fun i (c1, res1) ->
      bn_mul_f aLen a l j resLen res i (c1, res1)
    ) (u64 0, res) in
  assert (
    eval_i resLen res' (aLen + j) + uint_v c' * x_i (aLen + j) ==
    eval aLen a * uint_v l * x_i j + eval_i resLen res (aLen + j));
  c', res'

val bn_mul_f_pred1:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos
  -> b:lbignum bLen
  -> resLen:size_pos
  -> res:lbignum resLen{resLen = aLen + bLen}
  -> j:size_nat{j <= bLen}
  -> res':lbignum resLen
  -> Type0
let bn_mul_f_pred1 aLen a bLen b resLen res j res' =
  eval_i resLen res' (aLen + j) == eval aLen a * eval_i bLen b j

val bn_mul_f1:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos
  -> b:lbignum bLen
  -> resLen:size_nat{aLen + bLen = resLen /\ resLen + 1 < max_size_t}
  -> res:lbignum resLen
  -> repeatable #(lbignum resLen) #bLen (bn_mul_f_pred1 aLen a bLen b resLen res)
let bn_mul_f1 aLen a bLen b resLen res j res1 =
  assert (eval_i resLen res1 (aLen+j) = eval aLen a * eval_i bLen b j);
  let (c', res') = bn_mul_by_limb_addj aLen a b.[j] j resLen res1 in
  assert (eval_i resLen res' (aLen+j) + uint_v c' * x_i (aLen+j) == eval_i resLen res1 (aLen+j) + eval aLen a * uint_v b.[j] * x_i j);
  let res2 = res'.[aLen+j] <- c' in
  lemma_eval_equal1 resLen res2 resLen res' (aLen+j);
  assert (eval_i resLen res2 (aLen+j) == eval_i resLen res' (aLen+j));
  lemma_eval_incr resLen res2 (aLen+j+1);
  assert (eval_i resLen res2 (aLen+j+1) == eval_i resLen res2 (aLen+j) + uint_v res2.[aLen+j] * x_i (aLen+j)); //from eval_i
  assert (eval_i resLen res2 (aLen+j+1) == eval_i resLen res1 (aLen+j) + eval aLen a * uint_v b.[j] * x_i j - uint_v c' * x_i (aLen+j) + uint_v res2.[aLen+j] * x_i (aLen+j));
  assert (eval_i resLen res2 (aLen+j+1) == eval aLen a * eval_i bLen b j + eval aLen a * uint_v b.[j] * x_i j - uint_v c' * x_i (aLen+j) + uint_v res2.[aLen+j] * x_i (aLen+j));
  assert (uint_v res2.[aLen+j] == uint_v c');
  assert (eval_i resLen res2 (aLen+j+1) == eval aLen a * eval_i bLen b j + eval aLen a * uint_v b.[j] * x_i j);
  FStar.Math.Lemmas.paren_mul_right (eval aLen a) (uint_v b.[j]) (x_i j);
  FStar.Math.Lemmas.distributivity_add_right (eval aLen a) (eval_i bLen b j) (uint_v b.[j] * x_i j);
  assert (eval_i resLen res2 (aLen+j+1) == eval aLen a * (eval_i bLen b j + uint_v b.[j] * x_i j));
  lemma_eval_incr bLen b (j+1);
  res2

val bn_mul_:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos{aLen + bLen + 1 < max_size_t}
  -> b:lbignum bLen
  -> res:lbignum (aLen + bLen){eval (aLen+bLen) res == eval aLen a * eval bLen b}
let bn_mul_ aLen a bLen b =
  let resLen = aLen + bLen in
  let res = create resLen (u64 0) in
  lemma_eval_init_seq_is_0 resLen res aLen;
  assert (eval_i resLen res aLen = eval aLen a * eval_i bLen b 0);
  let res' =
    repeati_inductive bLen
    (bn_mul_f_pred1 aLen a bLen b resLen res)
    (fun j res1 ->
      bn_mul_f1 aLen a bLen b resLen res j res1
    ) res in
  res'

val lemma_bn_mul:
    #n:size_pos
  -> #m:size_pos
  -> a:bignum n
  -> b:bignum m
  -> Lemma (bn_v a * bn_v b < pow2 (n + m))
let lemma_bn_mul #n #m a b =
  assert (bn_v a * bn_v b < pow2 n * pow2 m);
  FStar.Math.Lemmas.pow2_plus n m

let bn_mul #nBits #mBits a b =
  let aLen = blocks nBits 64 in
  assert (nBits <= 64 * aLen);
  let a_bn = sub a.bn 0 aLen in
  lemma_eval_equal2 a.len a.bn aLen a_bn a.len;
  let bLen = blocks mBits 64 in
  let b_bn = sub b.bn 0 bLen in
  lemma_eval_equal2 b.len b.bn bLen b_bn b.len;
  let r = bn_mul_ aLen a_bn bLen b_bn in
  assert (eval (aLen+bLen) r == eval aLen a_bn * eval bLen b_bn);
  lemma_bn_mul a b;
  assert (eval (aLen+bLen) r < pow2 (nBits + mBits));
  let resLen = blocks (nBits+mBits) 64 in
  FStar.Math.Lemmas.pow2_le_compat (64*resLen) (nBits+mBits);
  let r1 = sub r 0 resLen in
  lemma_eval_pow2 (aLen+bLen) resLen r resLen;
  lemma_eval_equal2 (aLen+bLen) r resLen r1 resLen;
  let res:bignum (nBits+mBits) = Bignum resLen r1 in
  res

val lemma_lbignumndex:
    bLen:size_pos
  -> b:lbignum bLen
  -> i:size_nat{i < bLen}
  -> Lemma (uint_v b.[i] = eval bLen b / x_i i % x_i 1)
let lemma_lbignumndex bLen b i = admit()

val lemma_bignum_slice:
    bLen:size_pos
  -> b:lbignum bLen
  -> i:size_nat{i < bLen}
  -> j:size_nat{i < j /\ j < bLen}
  -> Lemma (eval (j - i) (slice b i j) < eval bLen b / x_i i % x_i (j - i))
let lemma_bignum_slice bLen b i j = admit()

let bn_get_bit #n b ind =
  let i = ind / 64 in
  let j = ind % 64 in
  lemma_lbignumndex b.len b.bn i;
  assert (uint_v b.bn.[i] == ((eval b.len b.bn) / (x_i i)) % x_i 1);
  let res = (uint_to_nat (b.bn.[i] >>. u32 j)) % 2 in
  assert (res == ((uint_v b.bn.[i]) / (pow2 j)) % 2);
  assert (res == ((((eval b.len b.bn) / (x_i i)) % x_i 1) / (pow2 j)) % 2);
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (eval b.len b.bn) (64*i) (64*(i+1));
  //assert (res == ((eval b.len b.bn) % x_i (i+1) / x_i i / pow2 j) % 2);
  FStar.Math.Lemmas.division_multiplication_lemma ((eval b.len b.bn) % x_i (i+1)) (x_i i) (pow2 j);
  assert (res == ((eval b.len b.bn) % x_i (i+1) / (x_i i * pow2 j)) % 2);
  FStar.Math.Lemmas.pow2_plus (64*i) j;
  FStar.Math.Lemmas.euclidean_division_definition ind 64;
  assert (res == ((eval b.len b.bn) % x_i (i+1) / (pow2 ind)) % 2);
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (eval b.len b.bn) ind (64*(i+1));
  assert (res == (((eval b.len b.bn) / (pow2 ind)) % pow2 (64*(i+1) - ind)) % 2);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 ((eval b.len b.bn) / (pow2 ind)) 1 (64*(i+1) - ind);
  res

val bn_get_bits_:
    len:size_nat
  -> b:lbignum len
  -> i:size_nat{i < len}
  -> j:size_nat{i < j /\ j <= len}
  -> lbignum (j - i)
let bn_get_bits_ len b i j = slice b i j

let bn_get_bits #n b i j =
  let i1 = i / 64 in
  let j1 = blocks j 64 in
  admit();
  let r = bn_get_bits_ b.len b.bn i1 j1 in
  assume (eval (j1 - i1) r < pow2 (j - i));
  let res:bignum (j - i) = Bignum (j1 - i1) r in
  assume (bn_v res == bn_v b / pow2 i % pow2 (j - i));
  res

let bn_rshift #n b i =
  let i1 = i / 64 in
  admit();
  let r = bn_get_bits_ b.len b.bn i1 b.len in
  assume (eval (b.len - i1) r < pow2 (n - i));
  let res:bignum (n - i) = Bignum (b.len - i1) r in
  assume (bn_v res == bn_v b / pow2 i);
  res

let bn_to_u64 b =
  let res = b.bn.[0] in
  assume (bn_v b == uint_v res);
  res

let bn_from_u64 c =
  let r = create 1 (u64 0) in
  let r = r.[0] <- c in
  assume (eval 1 r < pow2 64);
  let res:bignum 64 = Bignum 1 r in
  assume (bn_v res == uint_v c);
  res

val bn_is_less_f:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos
  -> b:lbignum bLen
  -> i:size_nat{i <= aLen}
  -> bool
let rec bn_is_less_f aLen a bLen b i =
  if i > 0 then
    let i = i - 1 in
    let t1 = a.[i] in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then
      if lt_u64 t1 t2 then true else false
    else bn_is_less_f aLen a bLen b i)
  else false

val bn_is_less_:
    aLen:size_pos
  -> a:lbignum aLen
  -> bLen:size_pos
  -> b:lbignum bLen
  -> res:bool{res = true ==> eval aLen a < eval bLen b}
let bn_is_less_ aLen a bLen b =
  let res = bn_is_less_f aLen a bLen b aLen in
  assume (res = true ==> eval aLen a < eval bLen b);
  res

let bn_is_less #n #m x y =
  admit();
  bn_is_less_ x.len x.bn y.len y.bn

val bn_lshift_mul_add_:
    aLen:size_pos
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_nat
  -> resLen:size_pos{aLen + j < resLen}
  -> res:lbignum resLen
  -> Pure (tuple2 carry (lbignum resLen))
    (requires True)
    (ensures fun (c', res') ->
      eval resLen res' + uint_v c' * pow2 resLen == eval aLen a * uint_v l * x_i j + eval resLen res)
let bn_lshift_mul_add_ aLen a l j resLen res =
  let c', res =
    repeati aLen
    (fun i (c, res) ->
      let c', res_ij = mul_carry_add_u64 a.[i] l c res.[i+j] in
      let res' = res.[i+j] <- res_ij in
      c', res'
    ) (u64 0, res) in
  let c_bn = create 1 (u64 0) in
  let c_bn = c_bn.[0] <- c' in

  let res1Len = resLen - (aLen + j) in
  let res1 = sub res (aLen + j) res1Len in
  admit();
  let c1, res1 = bn_add_ res1Len res1 1 c_bn in
  let res = update_sub res (aLen + j) res1Len res1 in
  c1, res

let bn_lshift_mul_add #n #m x i y z =
  admit();
  let i1 = i / 64 in
  let l = y.bn.[0] in
  let c1, r = bn_lshift_mul_add_ x.len x.bn l i1 z.len z.bn in
  let res:bignum m = Bignum z.len r in
  assume (64 * z.len == m);
  assume (eval z.len r + uint_v c1 * x_i z.len == eval x.len x.bn * pow2 i * eval y.len y.bn + eval z.len z.bn);
  res

let bn_lshift_add #n #m x i z =
  let i1 = i / 64 in
  admit();
  let x1 = create (i1 + x.len) (u64 0) in
  let x1 = update_sub x1 i1 x.len x.bn in
  let (c1, r) = bn_add_ z.len z.bn (i1 + x.len) x1 in
  let res:bignum m = Bignum z.len r in
  assume (64 * z.len == m);
  assume (eval z.len r + uint_v c1 * x_i z.len == eval x.len x.bn * pow2 i + eval z.len z.bn);
  res

let bn_from_bytes_be #bBytes b =
  let r = text_to_nat bBytes b in
  let rLen = blocks bBytes 8 in
  assume (eval rLen r < pow2 (8 * bBytes));
  let res:bignum (8*bBytes) = Bignum rLen r in
  assume (eval rLen r == nat_from_bytes_be b);
  res

let bn_to_bytes_be #bBits n =
  let bBytes = blocks bBits 8 in
  assume (8 * blocks bBytes 8 < max_size_t);
  assume (n.len == blocks bBytes 8);
  let b = nat_to_text bBytes n.bn in
  assume (eval n.len n.bn == nat_from_bytes_be b);
  b

val bn_set_bit:
     len:size_pos
  -> input:lbignum len
  -> ind:size_nat{ind / 64 < len}
  -> lbignum len
let bn_set_bit len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  input.[i] <- tmp |. (u64 1 <<. u32 j)

let bn_tbit = u64 0x8000000000000000

// res = a << 1
val bn_lshift1:
    aLen:size_pos
  -> a:lbignum aLen
  -> lbignum aLen
let bn_lshift1 aLen a =
  let res = create aLen (u64 0) in
  let c, res =
    repeati aLen
    (fun i (c, res) ->
      let tmp = a.[i] in
      let res = res.[i] <- (tmp <<. u32 1) |. c in
      let c = if eq_u64 (tmp &. bn_tbit) bn_tbit then u64 1 else u64 0 in
      c, res
    ) (u64 0, res) in
  res

// res = 2 ^^ p % a
val bn_pow2_mod_n:
    aBits:size_nat
  -> rLen:size_pos{aBits / 64 < rLen /\ rLen + 1 < max_size_t}
  -> a:lbignum rLen
  -> p:size_nat{aBits < p}
  -> lbignum rLen
let bn_pow2_mod_n aBits rLen a p =
  admit();
  let res = create rLen (u64 0) in
  let res = bn_set_bit rLen res aBits in
  let c, res = bn_sub_ rLen res (rLen-1) a in // res = res - a
  repeati (p - aBits)
  (fun i res ->
    let res = bn_lshift1 rLen res in
    if not (bn_is_less_ rLen res (rLen-1) a) then
      let c, res = bn_sub_ rLen res (rLen-1) a
      in res
    else res
  ) res

let bn_pow2_r_mod #nBits n r =
  admit();
  assume (nBits < r);
  let r1 = bn_pow2_mod_n nBits (n.len + 1) n.bn r in
  assume (eval n.len r1 < pow2 nBits);
  let res:bignum nBits = Bignum n.len r1 in
  assume (eval n.len r1 == (pow2 r) % (eval n.len n.bn));
  res
