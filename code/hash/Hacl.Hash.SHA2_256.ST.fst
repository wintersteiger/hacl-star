module Hacl.Hash.SHA2_256.ST

module Spec = Spec.SHA2_256.ST
open FStar.HyperStack.All
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open FStar.UInt32
open Spec
open Hacl.Hash.Lib.LoadStore
open Hacl.Hash.Lib.Create

#reset-options "--max_fuel 0  --z3rlimit 100"

(* IMPLEMENTATION of State Spec: Automatically generate? *)

let size_state  = 64ul (* k *) +^ 8ul (* h0 *) +^ 16ul (* data_w *) +^ 64ul (* ws_w *) +^ 
	          8ul  (* whash *) +^ 8ul (* whash_copy *) +^ 1ul (* len *)
type state = b:buffer Spec.u32{length b == v size_state}

let bufvalue (k:key) = b:buffer (value k){length b == seqlen k}
unfold let get_k (s:state) = Buffer.sub s 0ul 64ul
unfold let get_h0 (s:state) = Buffer.sub s 64ul 8ul
unfold let get_data (s:state) = Buffer.sub s 72ul 16ul
unfold let get_ws (s:state) = Buffer.sub s 88ul 64ul
unfold let get_whash (s:state) = Buffer.sub s 152ul 8ul
unfold let get_whash_copy (s:state) = Buffer.sub s 160ul 8ul
unfold let get_len (s:state) = Buffer.sub s 168ul 1ul

let get_buf (s:state) (k:key) = 
  match k with
 | K   -> get_k s
 | H0  -> get_h0 s
 | Data  -> get_data s
 | Ws  -> get_ws s
 | Whash  -> get_whash s
 | Whash_copy  -> get_whash_copy s
 | Len  -> get_len s
 | Pad -> admit()


let as_spec (h:mem) (s:state) : GTot (spec:state_spec{
  spec.k == as_seq h (get_k s) /\ 
  spec.h0 == as_seq h (get_h0 s) /\ 
  spec.data == as_seq h (get_data s) /\ 
  spec.ws == as_seq h (get_ws s) /\ 
  spec.whash == as_seq h (get_whash s) /\ 
  spec.whash_copy == as_seq h (get_whash_copy s) 
}) = {
  k = as_seq h (get_k s);
  h0 = as_seq h (get_h0 s);
  data = as_seq h (get_data s);
  ws = as_seq h (get_ws s);
  whash = as_seq h (get_whash s);
  whash_copy = as_seq h (get_whash_copy s);
  len = Seq.create 1 0;
  pad = Seq.create 128 0uy
}

let state_inv s = 
     let k = get_k s in
     let h0 = get_h0 s in
     let data = get_data s in
     let ws = get_ws s in
     let whash = get_whash s in
     let whash_copy = get_whash_copy s in
     let len = get_len s in
     length k == 64 /\
     length h0 == 8 /\
     length data == 16 /\
     length ws == 64 /\
     length whash == 8 /\
     length whash_copy == 8 /\
     length len == 1 /\
     disjoint k h0 /\ disjoint k data /\ disjoint k ws /\ disjoint k whash /\ disjoint k whash_copy /\ disjoint k len /\
     disjoint h0 data /\ disjoint h0 ws /\ disjoint h0 whash /\ disjoint h0 whash_copy /\ disjoint h0 len /\
     disjoint data ws /\ disjoint data whash /\ disjoint data whash_copy /\ disjoint data len /\
     disjoint ws whash /\ disjoint ws whash_copy /\ disjoint ws len /\
     disjoint whash whash_copy /\ disjoint whash len /\
     disjoint whash_copy len /\
     frameOf k == frameOf h0 /\
     frameOf k == frameOf data /\
     frameOf k == frameOf ws /\
     frameOf k == frameOf whash /\
     frameOf k == frameOf whash_copy /\
     frameOf k == frameOf len

let state_inv_st s h =
     state_inv s /\
     live h s /\
    ( let spec = as_spec h s in 
     spec.k == (snd (Spec.setup_k spec)).k /\
     spec.h0 == (snd (Spec.setup_h_0 spec)).k)

(* STATEFUL FUNCTIONANS WITH FUNCTIONAL SPEC *)
(*
unfold
type stateful 'b (spec:Spec.stateful 'b) = s:state -> Stack 'b
     (requires (fun h -> state_inv_st s h))
     (ensures (fun h0 r h1 -> state_inv_st s h1 /\
			    modifies_1 s h0 h1 
			    /\  (r,as_spec h1 s) == spec (as_spec h0 s) 
			    ))


let read (k:key) (x:u32{v x < seqlen k}) : stateful (Spec.value k) (Spec.read k (v x)) =
  fun st -> let b = get_buf st k in
	  b.(x)

let write (k:key) (x:u32{v x < seqlen k}) (vl:value k) : stateful unit (Spec.write k (v x) vl) =
  fun st -> let b = get_buf st k in
	  b.(x) <- vl
unfold let bind #s1 #s2 (f:stateful 'b s1) (g:x:'b -> stateful 'c (s2 x)) : stateful 'c (Spec.bind s1 s2) =
  fun st -> let r = f st in
	  g r st

let return (x:'b): stateful 'b  (Spec.return x) = fun st -> x

let as_seql h (b: buffer 'a) (l:nat{length b = l}) : GTot (Spec.Lib.seq_l 'a l) = as_seq h b

let apply_write (k:key) (#s:Spec.Lib.seq1_st (value k) (seqlen k) 'b)
    (f:b:buffer (value k) -> Stack 'b 
	      (requires (fun h -> live h b /\ length b = seqlen k))
	      (ensures (fun h0 r h1 -> live h1 b /\ modifies_1 b h0 h1 /\ length b = seqlen k /\
			  (r,as_seql h1 b (seqlen k)) == s (as_seql h0 b (seqlen k)))))
	      : stateful 'b (apply_write k s) =
   fun st -> f (get_buf st k)

assume val iteri:min:u32 -> max:u32{v min <= v max} -> 
	  #s:(x:nat{x >= v min /\ x < v max} -> Spec.stateful unit) -> 
	  f:(x:u32{v x >= v min /\ v x < v max} -> stateful unit (s (v x))) ->
	   stateful unit (Spec.iteri (v min) (v max) s)

*)
(* IGNORING FUNC CORRECTNESS: ONLY MEM SAFETY  *)

type stateful 'b = s:state -> Stack 'b
     (requires (fun h -> state_inv_st s h))
     (ensures (fun h0 r h1 -> state_inv_st s h1 /\ modifies_1 s h0 h1))


let read (k:key) (x:u32{v x < seqlen k}) : stateful (Spec.value k) =
  fun st -> let b = get_buf st k in
	  b.(x)

let write (k:key) (x:u32{v x < seqlen k}) (vl:value k) : stateful unit =
  fun st -> let b = get_buf st k in
	  b.(x) <- vl

unfold let bind (f:stateful 'b) (g:x:'b -> stateful 'c) : stateful 'c =
  fun st -> let r = f st in
	  g r st

let return (x:'b): stateful 'b  = fun st -> x

let apply_write (k:key) 
    (f:b:buffer (value k) -> Stack 'b 
	      (requires (fun h -> live h b /\ length b = seqlen k))
	      (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1)))
	      : stateful 'b =
   fun st -> f (get_buf st k)

assume val iteri: min:u32 -> max:u32{v min <= v max} -> 
	   f:(x:u32{v x >= v min /\ v x < v max} -> stateful unit) ->
	   stateful unit

(* BEGIN IMPL *)

let setup_k : stateful unit = fun st ->  hupd_64 (get_k st)
  (0x428a2f98ul) (0x71374491ul) (0xb5c0fbcful) (0xe9b5dba5ul)
  (0x3956c25bul) (0x59f111f1ul) (0x923f82a4ul) (0xab1c5ed5ul)
  (0xd807aa98ul) (0x12835b01ul) (0x243185beul) (0x550c7dc3ul)
  (0x72be5d74ul) (0x80deb1feul) (0x9bdc06a7ul) (0xc19bf174ul)
  (0xe49b69c1ul) (0xefbe4786ul) (0x0fc19dc6ul) (0x240ca1ccul)
  (0x2de92c6ful) (0x4a7484aaul) (0x5cb0a9dcul) (0x76f988daul)
  (0x983e5152ul) (0xa831c66dul) (0xb00327c8ul) (0xbf597fc7ul)
  (0xc6e00bf3ul) (0xd5a79147ul) (0x06ca6351ul) (0x14292967ul)
  (0x27b70a85ul) (0x2e1b2138ul) (0x4d2c6dfcul) (0x53380d13ul)
  (0x650a7354ul) (0x766a0abbul) (0x81c2c92eul) (0x92722c85ul)
  (0xa2bfe8a1ul) (0xa81a664bul) (0xc24b8b70ul) (0xc76c51a3ul)
  (0xd192e819ul) (0xd6990624ul) (0xf40e3585ul) (0x106aa070ul)
  (0x19a4c116ul) (0x1e376c08ul) (0x2748774cul) (0x34b0bcb5ul)
  (0x391c0cb3ul) (0x4ed8aa4aul) (0x5b9cca4ful) (0x682e6ff3ul)
  (0x748f82eeul) (0x78a5636ful) (0x84c87814ul) (0x8cc70208ul)
  (0x90befffaul) (0xa4506cebul) (0xbef9a3f7ul) (0xc67178f2ul)

let setup_h0 : stateful unit = fun st -> hupd_8 (get_h0 st)
  (0x6a09e667ul) (0xbb67ae85ul) (0x3c6ef372ul) (0xa54ff53aul)
  (0x510e527ful) (0x9b05688cul) (0x1f83d9abul) (0x5be0cd19ul)

let step_ws0 (i:u32{v i >= 0 /\ v i < 16}) : stateful unit =
     x <-- read Data i ;
     let y:u32 = x in
     write Ws i y 

let step_ws1 (i:u32{v i >= 16 /\ v i < 64}) : stateful unit =
    t16 <-- read Ws (i -^ 16ul) ;
    t15 <-- read Ws (i -^ 15ul) ;
    t7  <-- read Ws (i -^ 7ul)  ;
    t2  <-- read Ws (i -^ 2ul)  ;
    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    write Ws i (s1 +%^ (t7 +%^ (s0 +%^ t16)))

let setup_ws : stateful unit = 
  iteri 0ul 16ul step_ws0 ;;
  iteri 16ul 64ul step_ws1


let shuffle_core  (t:u32{v t >= 0 /\ v t < 64}) : stateful unit =
  a <-- read Whash 0ul ;
  b <-- read Whash 1ul ;
  c <-- read Whash 2ul ;
  d <-- read Whash 3ul ;
  e <-- read Whash 4ul ;
  f <-- read Whash 5ul ;
  g <-- read Whash 6ul ;
  h <-- read Whash 7ul ;
  kt <-- read K t ;
  wst <-- read Ws t ;
  
  let t1 = h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ kt +%^ wst in
  let t2 = (_Sigma0 a) +%^ (_Maj a b c) in

  write Whash 0ul (t1 +%^ t2);;
  write Whash 1ul a ;;
  write Whash 2ul b ;;
  write Whash 3ul c ;;
  write Whash 4ul (d +%^ t1);;
  write Whash 5ul e ;;
  write Whash 6ul f ;;
  write Whash 7ul g 


let shuffle : stateful unit = 
  iteri 0ul 64ul shuffle_core

let copy_whash: stateful unit = 
  iteri 0ul 8ul (fun i -> x <-- read Whash i; 
		    let x:u32 = x in write Whash_copy i x)

let sum_whash_copy: stateful unit = 
  iteri 0ul 8ul (fun i -> x <-- read Whash i; y <-- read Whash_copy i; write Whash i (x +%^ y))

let update_core : stateful unit = 
  copy_whash ;;
  shuffle ;;
  sum_whash_copy

let update (b:buffer u8{length b = 64}) (st:state{disjoint b st}) : Stack unit 
	   (requires (fun h -> state_inv_st st h /\ live h b))
	   (ensures (fun h _ h' -> state_inv_st st h' /\ modifies_1 st h h'))
    = 
  (apply_write Data (fun x -> uint32s_from_be_bytes x b 16ul);;
   update_core) st

let rec update_multi (n:u32) (blocks:buffer u8{length blocks == FStar.Mul.(v n * 64)}) 
		     (st:state{disjoint blocks st}) : Stack unit 
	   (requires (fun h -> state_inv_st st h /\ live h blocks))
	   (ensures (fun h _ h' -> state_inv_st st h' /\ modifies_1 st h h')) = 
  if n = 0ul then ()
  else
    let block = Buffer.sub blocks 0ul 64ul in
    let rem = Buffer.sub blocks 64ul ((n -^ 1ul) *^ 64ul) in
    update block st ;
    update_multi (n-^ 1ul) rem st


