module Vale.Arch.HeapImpl
open FStar.Mul
open Vale.Interop
open Vale.Def.Words_s
open Vale.Arch.MachineHeap_s
open Vale.Interop.Heap_s

noeq type vale_heap =
  | ValeHeap:
    mh:machine_heap ->
    mh0:machine_heap{is_machine_heap_update mh0 mh} ->
    ih0:Ghost.erased interop_heap{mh0 == down_mem (Ghost.reveal ih0)} ->
    to_heaplet_index:t_heaplet_map ->
    vale_heap

let get_heaplet_map vh = vh.to_heaplet_index

[@"opaque_to_smt"]
let _ih (vh:vale_heap) : GTot (ih:interop_heap{vh.mh == down_mem ih}) =
  let ih0 = Ghost.reveal vh.ih0 in
  let mh = vh.mh in
  up_down_identity ih0 mh;
  up_mem mh ih0

let mi_heap_upd (vh:vale_heap) (mh':machine_heap) : Pure vale_heap
  (requires is_machine_heap_update vh.mh mh')
  (ensures fun vh' -> vh'.mh == mh')
  =
  let ValeHeap _ mh0 ih0 thi = vh in
  up_down_identity (_ih vh) mh';
  ValeHeap mh' mh0 ih0 thi

