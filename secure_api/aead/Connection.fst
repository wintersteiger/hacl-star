module Connection
open FStar.HyperStack.ST
module AEAD = Crypto.AEAD.Main
module HH = FStar.HyperHeap
module I = Crypto.Indexing
(* module MM = FStar.MonotoneMap *)

assume val global_region :   AEAD.eternal_region
assume val doom_region   : r:AEAD.eternal_region{HH.disjoint global_region r}
noeq type pre_id = {
  reader_id : I.id;
  writer_id : I.id
}
type id = x:pre_id{x.reader_id =!= x.writer_id}

let peer_id (x:id) : id = {reader_id=x.writer_id; writer_id=x.reader_id}

assume val aead_log_region: #i:_ -> #rw:_ -> AEAD.aead_state i rw -> AEAD.eternal_region

#reset-options "--log_queries"
noeq type conn (i:id) =
  | MkConn: r:HH.rid
          -> w:HH.rid
          -> reader:AEAD.aead_state i.reader_id I.Reader{aead_log_region reader = r}
          -> writer:AEAD.aead_state i.writer_id I.Writer{aead_log_region writer = w}
          -> conn i
noeq
type addrs =
  | AllAddrs
  | SomeAddrs of TSet.set nat -> addrs
let fp = FStar.Map.t HH.rid addrs
module HS = FStar.HyperStack
let mutates (fp:fp) (h0:HS.mem) (h1:HS.mem) = 
  forall (r:HH.rid{r `is_in` h0}).
         if fp `Map.contains` r
         then match Map.sel fp r with 
              | AllAddrs -> r `is_in` h1
              | SomeAddrs addrs -> FStar.Heap.modifies_t addrs (Map.sel h0 r) (Map.sel h1 r)
         else (HH.sel h0 r == HH.sel h1 r /\ //the whole region didn't change
               h1 `Map.contains` r)
  
  ~ (fp `FStar.Map.contains` rid)
         /\ rid `Map.contains` h0 ==>
           HH.sel h0 rid == HH.sel h1 rid
  
  (rid, addrs) `TSet.mem` fp
               

let footprint #i (c:conn i) : TSet.set (HH.rid * option (TSet.set addr)) = 
  let w = MkConn?.writer c in
  let global_footpring = TSet.singleton (global_region * 
  AEAD.footprint writer //log_region + global

(* let peers #i #j (c:conn i) (d:conn j) = *)
(*   peer_id i = j /\ *)
(*   AEAD.peers (MkConn?.reader c) (MkConn?.writer c) /\ //implies that they share the same log *)
(*   AEAD.peers (MkConn?.writer c) (MkConn?.reader c) *)

(* let conn_inv #i (c:conn i) h = *)
(*   let MkConn _ _ reader writer = c in *)
(*   AEADInv reader h /\ *)
(*   AEADInv writer h *)

(* let my_nonce   (i:id) : nonce = let _reader_id, writer_id = i in AEAD.nonce writer_id *)
(* let peers_nonce (i:id) : nonce = let reader_id, _writer_id = i in AEAD.nonce reader_id *)

(* //////////////////////////////////////////////////////////////////////////////// *)

val nonce_to_region: MonotoneMap.id global_region nonce (fun _ -> rid) (fun table -> ...)

val conn_table: MonotoneMap.t global_region id conn (fun (table:DM.t id conn) ->
    (forall i j. if peer_id i = j then peers table.[i] table.[j]
            else footprint table.[i] `disjoint` footprint table.[j])

let global_inv (h:heap) =
  (forall i. conn_inv (h.[conn_table].[i]) h) /\
  (forall i. let c = h.[conn_table].[i] in
        let writer_region = MkConn?.w c in
        safeId i ==> h.[nonce_to_region].[my_nonce c] = writer_region)


let gen (i:id) (writer_region:rid) :
  ST (conn i)
     (requires (fun h -> safeId i ==> Some writer_region == nonce_to_region.[my_nonce i] /\
                      global_inv h0))
     (ensures (fun h0 c h1 -> modifies global_region h0 h1 /\
                           MkConn?.w = writer_region /\
                           global_inv h1 /\
                           conn_inv c h))
  = match !conn_table.[i] with
    | None -> //need to create both sides and put them in the table
      let my_writer, their_reader =
        AEAD.gen (snd i) writer_region in
      let their_region =
        match !nonce_to_region.[peers_nonce i] with
        | Some r -> r
        | None -> //this is a bad connection; it's doomed
          doom_region in
      let their_writer, my_reader =
        AEAD.gen (fst i) thei_region in
      let c = (MkConn their_region writer_region my_reader my_writer) in
      insert conn_table i c
      insert conn_table (peer_id i) (MkConn writer_region their_region their_reader their_writer);
      c
    | Some c -> c
