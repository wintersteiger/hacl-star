module Vale.Lib.Set
open FStar.Mul

friend FStar.Map
friend FStar.Set

let rec remove_between' s (start:int) (finish:int{start <= finish}) : Tot (s':S.set int{ forall i.
  ((start <= i /\ i < finish) ==> not (S.mem i s')) /\
  ((i < start \/ finish <= i) ==> S.mem i s' = S.mem i s)})
  (decreases %[finish - start]) =
  if finish = start then s
  else remove_between' (S.intersect s (S.complement (S.singleton start))) (start + 1) finish

let remove_between s start finish =
  if finish <= start then s
  else remove_between' s start finish

let remove_between_reveal s start finish i = ()

let lemma_sel_restrict #a s m k = ()

assume val _set_restrict (#t:eqtype) (s:S.set t) (p:t -> bool) : Pure (S.set t)
  (requires True)
  (ensures fun r -> forall x.{:pattern (S.mem x r)} S.mem x r <==> S.mem x s /\ p x)

let set_restrict #t s p =
  _set_restrict s p
//  let f x = s x && p x in
//  FStar.FunctionalExtensionality.on_dom t f

let lemma_set_restrict #t s p = ()
