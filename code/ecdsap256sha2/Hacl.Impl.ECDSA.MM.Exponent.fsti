module Hacl.Impl.ECDSA.MM.Exponent


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Spec.P256.Lemmas
open Spec.ECDSAP256.Definition
open Spec.ECDSA
open Hacl.Impl.LowLevel
open Spec.P256.Ladder

open Spec.P256.Lemmas

open FStar.Mul

open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Lib.Loops

#reset-options " --z3rlimit 200"

noextract
let order = Spec.P256.order

val montgomery_ladder_exponent: a: felem -> Stack unit 
  (requires fun h -> live h a /\ as_nat h a < order)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    (
      let b_ = fromDomain_ (as_nat h0 a) in 
      let r0D = exponent_spec b_ in 
      fromDomain_ (as_nat h1 a) == r0D /\
      as_nat h1 a < order
    )
)

val fromDomainImpl: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat h a < order)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
     as_nat h1 result < order /\ as_nat h1 result == fromDomain_ (as_nat h0 a))

val multPower: a: felem -> b: felem ->  result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < order /\ as_nat h b < order)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = (pow (as_nat h0 a) (order - 2)  * (as_nat h0 b)) % order)


val multPowerPartial: s: felem -> a: felem -> b: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < order /\ as_nat h b < order /\ 
  (
      let a_ = fromDomain_  (fromDomain_ (as_nat h s)) in 
      let r0D = exponent_spec a_ in 
      fromDomain_ (as_nat h a) == r0D)
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = (pow (as_nat h0 s) (order - 2)  * (as_nat h0 b)) % order)
