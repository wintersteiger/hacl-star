module Vale.Arch.Heap
open FStar.Mul
open Vale.Def.Words_s
open Vale.Arch.MachineHeap_s
open Vale.Interop.Heap_s

// This module defines the heap interface, called heap_impl, seen by Vale.X64.Machine_Semantics_s.
// The interface is a trusted specification, but its implementation is defined in untrusted code.

val heap_impl : Type u#1

val heap_get (hi:heap_impl) : machine_heap

val heap_upd (hi:heap_impl) (mh':machine_heap) : Pure heap_impl
  (requires is_machine_heap_update (heap_get hi) mh')
  (ensures fun hi -> heap_get hi == mh')

val heap_of_interop (ih:interop_heap) : GTot heap_impl

val heap_get_unchanged_memory (hi:heap_impl) : heap_impl

val heap_get_heaplet (hi:heap_impl) (idx:int) : machine_heap

val heap_upd_heaplet (hi:heap_impl) (idx:int) (mh':machine_heap) : Pure heap_impl
  (requires (is_machine_heap_update (heap_get_heaplet hi idx) mh'))
  (ensures fun hi' ->
      (heap_get_unchanged_memory hi' == heap_get_unchanged_memory hi) /\
      (heap_get_heaplet hi' idx == mh') /\
      (forall idx'. idx' <> idx ==> heap_get_heaplet hi' idx' == heap_get_heaplet hi idx'))

val heap_extensional_equality (hi1 hi2:heap_impl) :
  Lemma
    (requires (
        heap_get_unchanged_memory hi1 == heap_get_unchanged_memory hi2 /\
        (forall idx. heap_get_heaplet hi1 idx == heap_get_heaplet hi2 idx)))
    (ensures (hi1 == hi2))
