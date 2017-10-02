module Spec.Lib

module ST = FStar.HyperStack.ST

open FStar.Seq
open FStar.UInt32
open FStar.Endianness

let op_Star_Star = FStar.Mul.op_Star

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

let rotate_left (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) : Tot UInt32.t =
  ((a <<^ s) |^ (a >>^ (32ul -^ s)))

let rotate_right (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) : Tot UInt32.t =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

let op_Less_Less_Less (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) = rotate_left a s
let op_Greater_Greater_Greater (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) = rotate_right a s

let byte = UInt8.t
let bytes = seq UInt8.t
let lbytes (l:nat) = b:seq UInt8.t {length b = l}
let op_At f g = fun x -> g (f x)
let op_Bar_Greater f g = op_At f g
inline_for_extraction
let set (i:nat) (x:'a) (s:seq 'a{length s > i}) : Tot (s':seq 'a{length s' = length s}) = upd s i x
inline_for_extraction
let op_String_Access = Seq.index
inline_for_extraction
let op_String_Assignment = Seq.upd

unfold inline_for_extraction
let iter n f x = Spec.Loops.repeat_spec n f x

unfold inline_for_extraction
let map2 f s1 s2 = Spec.Loops.seq_map2 f s1 s2

let singleton x = Seq.create 1 x

let tuple x y = Seq.upd (Seq.create 2 x) 1 y

#set-options "--initial_fuel 0 --max_fuel 0"

let uint32_from_le (b:lbytes 4) : UInt32.t =
    let n = little_endian b  in
    lemma_little_endian_is_bounded b;
    UInt32.uint_to_t n

let uint32_to_le (a:UInt32.t) : lbytes 4 =
    little_bytes 4ul (v a)

let uint32_from_be (b:lbytes 4) : UInt32.t =
    let n = big_endian b  in
    lemma_big_endian_is_bounded b;
    UInt32.uint_to_t n

let uint32_to_be (a:UInt32.t) : lbytes 4 =
    big_bytes 4ul (v a)


let uint64_from_le (b:lbytes 8) : UInt64.t =
    let n = little_endian b  in
    lemma_little_endian_is_bounded b;
    UInt64.uint_to_t n

let uint64_to_le (a:UInt64.t) : lbytes 8 =
    little_bytes 8ul (UInt64.v a)

let uint64_from_be (b:lbytes 8) : UInt64.t =
    let n = big_endian b  in
    lemma_big_endian_is_bounded b;
    UInt64.uint_to_t n

let uint64_to_be (a:UInt64.t) : lbytes 8 =
    big_bytes 8ul (UInt64.v a)


let lemma_uint32_from_le_inj (b:lbytes 4) (b':lbytes 4) : Lemma
  (requires (uint32_from_le b = uint32_from_le b'))
  (ensures  (b == b'))
  = lemma_little_endian_inj b b'


let lemma_uint32_to_le_inj (b:UInt32.t) (b':UInt32.t) : Lemma
  (requires (uint32_to_le b == uint32_to_le b'))
  (ensures  (b = b'))
  = ()

let lemma_uint32_to_from_bij (b:UInt32.t) : Lemma
  (requires (True))
  (ensures (uint32_from_le (uint32_to_le b) = b))
  = ()

let lemma_uint32_from_to_bij (b:lbytes 4) : Lemma
  (requires (True))
  (ensures (uint32_to_le (uint32_from_le b) = b))
  = lemma_uint32_to_from_bij (uint32_from_le b);
    let lemma (s:lbytes 4) (s':lbytes 4):
      Lemma (requires (s <> s'))
            (ensures (uint32_from_le s <> uint32_from_le s'))
      = if uint32_from_le s = uint32_from_le s' then lemma_uint32_from_le_inj s s' in
    if uint32_to_le (uint32_from_le b) <> b then lemma (uint32_to_le (uint32_from_le b)) b


val uint32s_from_le: len:nat -> b:lbytes (4 ** len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_le len src =
  if len = 0 then createEmpty
  else (
    let prefix, last = split src (4 ** len - 4) in
    snoc (uint32s_from_le (len-1) prefix) (uint32_from_le last)
  )

val uint32s_to_le: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 ** len))  (decreases len)
let rec uint32s_to_le len src =
  if len = 0 then createEmpty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint32s_to_le (len-1) prefix @| (uint32_to_le last)
  )

val uint64s_from_le: len:nat -> b:lbytes (8 ** len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_le len src =
  if len = 0 then createEmpty
  else (
    let prefix, last = split src (8 ** len - 8) in
    snoc (uint64s_from_le (len-1) prefix) (uint64_from_le last)
  )

val uint64s_to_le: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 ** len))  (decreases len)
let rec uint64s_to_le len src =
  if len = 0 then createEmpty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint64s_to_le (len-1) prefix @| (uint64_to_le last)
  )


val uint32s_from_be: len:nat -> b:lbytes (4 ** len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_be len src =
  if len = 0 then createEmpty
  else (
    let prefix, last = split src (4 ** len - 4) in
    snoc (uint32s_from_be (len-1) prefix) (uint32_from_be last)
  )

val uint32s_to_be: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 ** len))  (decreases len)
let rec uint32s_to_be len src =
  if len = 0 then createEmpty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint32s_to_be (len-1) prefix @| (uint32_to_be last)
  )

val uint64s_from_be: len:nat -> b:lbytes (8 ** len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_be len src =
  if len = 0 then createEmpty
  else (
    let prefix, last = split src (8 ** len - 8) in
    snoc (uint64s_from_be (len-1) prefix) (uint64_from_be last)
  )

val uint64s_to_be: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 ** len))  (decreases len)
let rec uint64s_to_be len src =
  if len = 0 then createEmpty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint64s_to_be (len-1) prefix @| (uint64_to_be last)
  )


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let lemma_uint32s_from_le_def_0 (len:nat{len = 0}) (b:lbytes (4**len)) : Lemma
  (uint32s_from_le len b == Seq.createEmpty)
  = ()
let lemma_uint32s_from_le_def_1 (len:nat{len > 0}) (b:lbytes (4**len)) : Lemma
  (uint32s_from_le len b == Seq.snoc (uint32s_from_le (len-1) (slice b 0 (4**len - 4)))
                                     (uint32_from_le (slice b (4**len - 4) (4**len)))
  )
  = ()


let lemma_uint32s_to_le_def_0 (len:nat{len = 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.createEmpty)
  = ()
let lemma_uint32s_to_le_def_1 (len:nat{len > 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.append (uint32s_to_le (len-1) (slice s 0 (len-1)))
                                     (uint32_to_le (index s (len-1))))
  = ()


let lemma_uint32s_from_be_def_0 (len:nat{len = 0}) (b:lbytes (4**len)) : Lemma
  (uint32s_from_be len b == Seq.createEmpty)
  = ()
let lemma_uint32s_from_be_def_1 (len:nat{len > 0}) (b:lbytes (4**len)) : Lemma
  (uint32s_from_be len b == Seq.snoc (uint32s_from_be (len-1) (slice b 0 (4**len - 4)))
                                     (uint32_from_be (slice b (4**len - 4) (4**len)))
  )
  = ()


let lemma_uint32s_to_be_def_0 (len:nat{len = 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_be len s == Seq.createEmpty)
  = ()
let lemma_uint32s_to_be_def_1 (len:nat{len > 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_be len s == Seq.append (uint32s_to_be (len-1) (slice s 0 (len-1)))
                                     (uint32_to_be (index s (len-1))))
  = ()


let lemma_uint64s_from_be_def_0 (len:nat{len = 0}) (b:lbytes (8**len)) : Lemma
  (uint64s_from_be len b == Seq.createEmpty)
  = ()
let lemma_uint64s_from_be_def_1 (len:nat{len > 0}) (b:lbytes (8**len)) : Lemma
  (uint64s_from_be len b == Seq.snoc (uint64s_from_be (len-1) (slice b 0 (8**len - 8)))
                                     (uint64_from_be (slice b (8**len - 8) (8**len)))
  )
  = ()


let lemma_uint64s_to_be_def_0 (len:nat{len = 0}) (s:seq UInt64.t{length s = len}) : Lemma
  (uint64s_to_be len s == Seq.createEmpty)
  = ()
let lemma_uint64s_to_be_def_1 (len:nat{len > 0}) (s:seq UInt64.t{length s = len}) : Lemma
  (uint64s_to_be len s == Seq.append (uint64s_to_be (len-1) (slice s 0 (len-1)))
                                     (uint64_to_be (index s (len-1))))
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let rec lemma_uint32s_from_le_inj (len:nat) (b:lbytes (4 ** len)) (b':lbytes (4 ** len)) : Lemma
  (requires (uint32s_from_le len b == uint32s_from_le len b'))
  (ensures  (b == b'))
  = if len = 0 then (lemma_uint32s_from_le_def_0 len b; lemma_uint32s_from_le_def_0 len b';
      Seq.lemma_eq_intro b b')
    else (
          let h  = slice b (4**len - 4) (4**len) in
          let h'  = slice b' (4**len - 4) (4**len) in
          let t  = slice b 0 (4**len-4) in
          let t' = slice b' 0 (4**len-4) in
          lemma_uint32s_from_le_def_1 len b;
          lemma_uint32s_from_le_def_1 len b';
          Seq.lemma_eq_intro (uint32s_from_le len b) (uint32s_from_le len b');
          cut (Seq.index (uint32s_from_le len b) (len-1) == Seq.index (uint32s_from_le len b') (len-1));
          cut (Seq.index (uint32s_from_le len b) (len-1) == uint32_from_le h);
          cut (Seq.index (uint32s_from_le len b') (len-1) == uint32_from_le h');
          lemma_uint32_from_le_inj h h';
          Seq.lemma_eq_intro h h';
          cut (Seq.slice (uint32s_from_le len b) 0 (len-1) == Seq.slice (uint32s_from_le len b') 0 (len-1));
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b) 0 (len-1)) (uint32s_from_le (len-1) t);
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b') 0 (len-1)) (uint32s_from_le (len-1) t');
          lemma_uint32s_from_le_inj (len-1) t t';
          Seq.lemma_eq_intro t t';
          Seq.lemma_eq_intro b (t @| h);
          Seq.lemma_eq_intro b' (t' @| h')
          )


#set-options "--max_fuel 0 --z3rlimit 100"

let rec lemma_uint32s_from_le_bij (len:nat) (b:lbytes (4 ** len)) : Lemma
  (requires (True))
  (ensures  (uint32s_to_le len (uint32s_from_le len b) == b))
  = if len = 0 then (
      lemma_uint32s_from_le_def_0 0 b;
      lemma_uint32s_to_le_def_0 0 (createEmpty);
      lemma_eq_intro (uint32s_to_le len (uint32s_from_le len b)) b
    ) else (
      lemma_uint32s_from_le_def_1 len b;
      let b' = uint32s_from_le len b in
      lemma_uint32s_to_le_def_1 len b';
      lemma_uint32_from_to_bij (slice b (4**len-4) (length b));
      lemma_uint32s_from_le_bij (len - 1) (slice b 0 (length b - 4));
      lemma_eq_intro b'  (snoc (uint32s_from_le (len-1) (slice b 0 (length b - 4))) (uint32_from_le (slice b (length b - 4) (length b))));
      lemma_eq_intro (slice b' 0 (length b'-1)) (uint32s_from_le (len-1) (slice b 0 (length b - 4)));
      lemma_eq_intro (uint32s_to_le len b') (append (uint32s_to_le (len-1) (uint32s_from_le (len-1) (slice b 0 (length b - 4)))) (uint32_to_le (uint32_from_le (slice b (length b - 4) (length b)))) );
      lemma_eq_intro (uint32s_to_le len (uint32s_from_le len b)) b
    )

let rec lemma_uint32s_to_le_inj (len:nat) (b:seq UInt32.t{length b = len})
                                         (b':seq UInt32.t{length b' = len})  : Lemma
  (requires (uint32s_to_le len b == uint32s_to_le len b'))
  (ensures  (b == b'))
  = if len = 0 then (
      lemma_uint32s_to_le_def_0 len b;
      lemma_uint32s_to_le_def_0 len b';
      Seq.lemma_eq_intro b b'
    ) else (
      let h  = index b (len-1) in
      let h' = index b' (len-1) in
      let t  = slice b 0 (len-1) in
      let t' = slice b' 0 (len-1) in
      lemma_uint32s_to_le_def_1 len b;
      lemma_uint32s_to_le_def_1 len b';
      Seq.lemma_eq_intro (uint32s_to_le len b) (uint32s_to_le len b');
      cut (Seq.slice (uint32s_to_le len b) (4**len-4) (4 ** len) == Seq.slice (uint32s_to_le len b') (4**len -4) (4 ** len));
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) (4**len-4) (4 ** len)) (uint32_to_le h);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') (4**len-4) (4 ** len)) (uint32_to_le h');
      lemma_uint32_to_le_inj h h';
      cut (Seq.slice (uint32s_to_le len b) 0 (4**len-4) == Seq.slice (uint32s_to_le len b') 0 (4**len-4));
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) 0 (4**len-4)) (uint32s_to_le (len-1) t);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') 0 (4**len-4)) (uint32s_to_le (len-1) t');
      lemma_uint32s_to_le_inj (len-1) t t';
      Seq.lemma_eq_intro t t';
      Seq.lemma_eq_intro b (snoc t h);
      Seq.lemma_eq_intro b' (snoc t' h')
    )


let rec lemma_uint32s_to_le_bij (len:nat) (b:seq UInt32.t{length b = len}) : Lemma
  (requires (True))
  (ensures  (uint32s_from_le len (uint32s_to_le len b) == b))
  = if len = 0 then (
      lemma_uint32s_to_le_def_0 0 b;
      lemma_uint32s_from_le_def_0 0 (createEmpty);
      lemma_eq_intro (uint32s_from_le len (uint32s_to_le len b)) b
    ) else (
      lemma_uint32s_to_le_def_1 len b;
      let b' = uint32s_to_le len b in
      lemma_uint32s_from_le_def_1 len b';
      lemma_uint32_to_from_bij (index b (len-1));
      lemma_uint32s_to_le_bij (len - 1) (slice b 0 (length b-1));
      lemma_eq_intro b' (append (uint32s_to_le (len-1) (slice b 0 (length b-1))) (uint32_to_le (index b (len-1))));
      lemma_eq_intro (slice b' 0 (length b' - 4)) (uint32s_to_le (len-1) (slice b 0 (length b-1)));
      lemma_eq_intro (slice b' (4**len-4) (4**len)) (uint32_to_le (index b (len-1)));
      lemma_eq_intro (uint32s_from_le len b') (snoc (uint32s_from_le (len-1) (uint32s_to_le (len-1) (slice b 0 (length b-1)))) (uint32_from_le (uint32_to_le (index b (len-1)))));
      lemma_eq_intro (uint32s_from_le len (uint32s_to_le len b)) b
    )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

let lemma_append_assoc (#a:Type) (x:seq a) (y:seq a) (z:seq a) : Lemma
  (x @| (y @| z) == (x @| y) @| z) = lemma_eq_intro ((x @| y) @| z) (x @| (y @| z))


val lemma_uint32s_from_le_slice: len:nat -> b:lbytes (4**len) -> n:nat{n <= len} -> Lemma
  (requires (True))
  (ensures (uint32s_from_le len b == uint32s_from_le n (slice b 0 (4 ** n)) @| uint32s_from_le (len - n) (slice b (4 ** n) (length b))))
  (decreases (len-n))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"
let rec lemma_uint32s_from_le_slice len b n =
  if n = len then (
    lemma_uint32s_from_le_def_0 0 (slice b (4**len) (4**len));
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_from_le 0 (slice b (4**len) (4**len))) createEmpty;
    lemma_eq_intro (uint32s_from_le len b @| createEmpty) (uint32s_from_le len b)
  ) else (
    lemma_uint32s_from_le_def_1 len b;
    lemma_uint32s_from_le_def_1 (len - n) (slice b (4 ** n) (4 ** len));
    let tl, hd = split b (4**len - 4) in
    lemma_uint32s_from_le_slice (len-1) tl (n);
    lemma_eq_intro (slice tl 0 (4**n)) (slice b 0 (4**n));
    lemma_eq_intro (slice tl (4**n) (4**(len-1))) (slice b (4**n) (4 ** (len - 1)));
    lemma_append_assoc (uint32s_from_le n (slice tl 0 (4 ** n)))
                       (uint32s_from_le (len - 1 - n) (slice tl (4**n) (4**(len - 1))))
                       (create 1 (uint32_from_le hd));
    lemma_eq_intro (slice b (4**len-4) (4**len)) (slice (slice b (4**n) (4**len)) (4**(len - 1 - n)) (4**(len-n)));
    lemma_eq_intro (slice b (4**n) (4**(len-1))) (slice (slice b (4**n) (length b)) 0 (4 ** (len - n - 1)));

    lemma_eq_intro (uint32s_from_le (len-n) (slice b (4 ** n) (4**len))) (snoc (uint32s_from_le (len-n-1) (slice b (4**n) (4**(len-1)))) (uint32_from_le hd)))


val lemma_uint32s_to_le_slice: len:nat -> b:Seq.seq UInt32.t{length b = len} -> n:nat{n <= len} -> Lemma
  (requires (True))
  (ensures (uint32s_to_le len b = uint32s_to_le n (slice b 0 n) @| uint32s_to_le (len - n) (slice b n len)))
  (decreases (len - n))
let rec lemma_uint32s_to_le_slice len b n =
  if n = len then (
    lemma_uint32s_to_le_def_0 0 (slice b len len);
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_to_le 0 (slice b len len)) createEmpty;
    lemma_eq_intro (uint32s_to_le len b @| createEmpty) (uint32s_to_le len b)
  ) else (
    lemma_uint32s_to_le_def_1 len b;
    lemma_uint32s_to_le_def_1 (len-n) (slice b n (len));
    let h  = index b (len-1) in
    let tl = slice b 0 (len-1) in
    lemma_uint32s_to_le_slice (len-1) tl (n);
    lemma_eq_intro (slice tl (0) (n)) (slice b 0 n);
    lemma_eq_intro (slice tl n (len - 1)) (slice b n (len - 1));
    lemma_append_assoc (uint32s_to_le (n) (slice b 0 n))
                       (uint32s_to_le (len-n-1) (slice b n (len-1))) (uint32_to_le h);
    cut (index (slice b n len) (len - n - 1) = index b (len-1));
    lemma_eq_intro (slice b n (len-1)) (slice (slice b n (len)) 0 (len-n-1));
    lemma_eq_intro (uint32s_to_le (len-n) (slice b n (len))) (uint32s_to_le (len-n-1) (slice b n (len-1)) @| uint32_to_le h)
  )

(** Generic key-value state monad: WIP **)
noeq 
type kv (a:Type) = 
  |  MkSt: k: Type -> v: Type -> 
	   get:(a -> k -> Tot v) -> 
	   set:(a -> k -> v -> Tot a) -> kv a

     
type stateful (a:Type) (b:Type) =
	      a -> Tot (b * a)

val stateful_read: #a:Type -> kv:kv a -> key:kv.k -> Tot (stateful a kv.v)	   
let stateful_read  #a kv key = 
    fun m -> kv.get m key, m

val stateful_write: #a:Type -> kv:kv a -> key:kv.k -> value:kv.v -> Tot (stateful a unit)	   
let stateful_write  #a kv key value = 
    fun m -> (), kv.set m key value

val stateful_return: #a: Type -> #b:Type -> r:b -> Tot (stateful a b)
let stateful_return #a #b r = 
    fun m -> r, m
    
val stateful_bind: #a:Type -> #b:Type -> #c:Type -> stateful a b -> (b -> Tot (stateful a c)) -> Tot (stateful a c)
let stateful_bind #a #b #c f g = fun s -> let (a,s) = f s in g a s

type u32 = FStar.UInt32.t

// state monad for manipulating one sequence
type seq_l 'a n = m: seq 'a{length m = n}
type index_l n = m: nat{m < n}
type seq1_st s n b =
     seq_l s n -> Tot (b * seq_l s n)

unfold val seq1_read: #a:Type -> #n:nat -> (i:index_l n) -> Tot (seq1_st a n a)
unfold let seq1_read  #a #n i = fun m -> Seq.index m i, m

unfold val seq1_copy: #a:Type -> #n:nat -> Tot (seq1_st a n (seq_l a n))
unfold let seq1_copy  #a #n = fun m -> m, m


val seq1_return: #a:Type -> #n:nat -> #b:Type -> x:b -> seq1_st a n b
let seq1_return #a #n #b w = fun m -> (w,m)

unfold val seq1_write: #a:Type -> #n:nat -> (i:index_l n) -> (v:a) -> Tot (seq1_st a n unit)
unfold let seq1_write #a #n i x = fun m ->  (), (m.[i] <- x)

unfold val seq1_bind: #a:Type -> #n:nat -> #b:Type -> #c:Type -> seq1_st a n b -> (b -> seq1_st a n c) -> Tot (seq1_st a n c)
unfold let seq1_bind #a #n #b #c f g = fun s -> let a, s = f s in g a s

val seq1_iter: #a:Type -> #n:nat -> c:nat -> seq1_st a n unit -> Tot (seq1_st a n unit)
let seq1_iter #a #m n f = 
    let f' (s:seq_l a m) : Tot (seq_l a m) = 
        let s' = f s in
	snd s'
    in
    fun s -> (),iter n f' s

val seq1_iteri: #a:Type -> #n:nat -> c:nat -> (nat -> seq1_st a n unit) -> Tot (seq1_st a n unit)
let seq1_iteri #a #m n f = 
    let f' (s:seq_l a m) i : Tot (seq_l a m) = 
        let s' = f i s in
	snd s'
    in
    fun s -> (),Spec.Loops.repeat_range_spec 0 n f' s

val seq1_in_place_map2: #a:Type -> #n:nat -> #b:Type -> f:(a -> b -> Tot a) -> s:seq_l b n -> Tot (seq1_st a n unit)
let seq1_in_place_map2  #a #m #b f i = 
    fun s -> 
      let s' = Spec.Loops.seq_map2 f s i in
      (),s'

val seq1_alloc: #a:Type -> #n:nat -> #b:Type -> init:a -> f:seq1_st a n b -> Tot b
let seq1_alloc #a #n #b init f =
    let s = Seq.create n init in
    let s' = f s in
    fst s'

val seq1_uint32s_from_le: #n:nat -> b:bytes -> start:nat -> len: nat{
						     length b = (4 ** len)
					 	   /\ start + len <= n} -> 
		     Tot (seq1_st u32 n unit) 
let seq1_uint32s_from_le #n src start len =
  fun s ->
    let s' = uint32s_from_le len src in
    let s0,s_ = split s start in
    let s1,s2 = split s_ len in
    (), s0 @| s' @| s2

val seq1_uint32s_from_be: #n:nat -> b:bytes -> start:nat -> len: nat{
						     length b = (4 ** len)
					 	   /\ start + len <= n} -> 
		     Tot (seq1_st u32 n unit) 
let seq1_uint32s_from_be #n src start len =
  fun s ->
    let s' = uint32s_from_be len src in
    let s0,s_ = split s start in
    let s1,s2 = split s_ len in
    (), s0 @| s' @| s2

val seq1_uint32s_to_le: #n:nat -> start:nat -> len: nat{start + len <= n} -> 
		     Tot (seq1_st u32 n (lbytes (4 ** len)))
let seq1_uint32s_to_le #n start len =
  fun s ->
    if len = 0 then
       Seq.createEmpty, s
    else
       let s0,s_ = split s start in
       let s1,s2 = split s_ len in
       let b = uint32s_to_le len s1 in
       b, s

val seq1_uint32s_to_be: #n:nat -> s:seq u32{length s == n} -> 
			Tot (seq1_st u8 (4 ** n) unit)
let seq1_uint32s_to_be #n inp =
  fun s ->
       let b = uint32s_to_be n inp in
       (), b



let seq1_upd8 #a #n (start:nat{start + 8 <= n}) x0 x1 x2 x3 x4 x5 x6 x7 : seq1_st a n unit = 
  let bind = seq1_bind in
  seq1_write #a #n start x0 ;;
  seq1_write #a #n (start + 1) x1;;
  seq1_write #a #n (start + 2) x2;;
  seq1_write #a #n (start + 3) x3;;
  seq1_write #a #n (start + 4) x4;;
  seq1_write #a #n (start + 5) x5;;
  seq1_write #a #n (start + 6) x6;;
  seq1_write #a #n (start + 7) x7

  

let seq1_upd16 #a #n (start:nat{start + 16 <= n}) x0 x1 x2 x3 x4 x5 x6 x7 
  x8 x9 x10 x11 x12 x13 x14 x15 : seq1_st a n unit = 
  let bind = seq1_bind in
  seq1_upd8 #a #n start x0 x1 x2 x3 x4 x5 x6 x7;;
  seq1_upd8 #a #n (start + 8) x8 x9 x10 x11 x12 x13 x14 x15


let seq1_upd32 #a #n (start:nat{start + 32 <= n}) 
  x0 x1 x2 x3 x4 x5 x6 x7 
  x8 x9 x10 x11 x12 x13 x14 x15 
  x16 x17 x18 x19 x20 x21 x22 x23
  x24 x25 x26 x27 x28 x29 x30 x31   
  : seq1_st a n unit = 
  let bind = seq1_bind in
  seq1_upd16 #a #n start x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15;;
  seq1_upd16 #a #n (start + 16)  x16 x17 x18 x19 x20 x21 x22 x23  x24 x25 x26 x27 x28 x29 x30 x31 


let seq1_upd64 #a 
  (x0:a) (x1:a) (x2:a) (x3:a) (x4:a) (x5:a) (x6:a) (x7  :a) (x8:a) (x9:a) (x10:a) (x11:a) (x12:a) (x13:a) (x14:a) (x15  :a) (x16:a) (x17:a) (x18:a) (x19:a) (x20:a) (x21:a) (x22:a) (x23 :a) (x24:a) (x25:a) (x26:a) (x27:a) (x28:a) (x29:a) (x30:a) (x31 :a) (y0:a) (y1:a) (y2:a) (y3:a) (y4:a) (y5:a) (y6:a) (y7  :a) (y8:a) (y9:a) (y10:a) (y11:a) (y12:a) (y13:a) (y14:a) (y15  :a) (y16:a) (y17:a) (y18:a) (y19:a) (y20:a) (y21:a) (y22:a) (y23 :a) (y24:a) (y25:a) (y26:a) (y27:a) (y28:a) (y29:a) (y30:a) (y31:a)   
  : seq1_st a 64 unit = 
  let bind = seq1_bind #a #64 #unit #unit in
  seq1_upd32 #a #64 0  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
		 x16 x17 x18 x19 x20 x21 x22 x23  x24 x25 x26 x27 x28 x29 x30 x31 ;;
  seq1_upd32 #a #64 32 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
		 y16 y17 y18 y19 y20 y21 y22 y23  y24 y25 y26 y27 y28 y29 y30 y31 

