module

import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialIndependence

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) (x : MilnorKRing (AdjoinRoot (poly p))) :
    simpleMilnorNorm q (milnorKRingMap ε.toRingHom x) = simpleMilnorNorm p x :=
  simpleMilnorNorm_map_algEquiv p q ε x

example
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) :
    (simpleMilnorNorm q).comp (milnorKRingMap ε.toRingHom).toAddMonoidHom =
      simpleMilnorNorm p :=
  simpleMilnorNorm_comp_map_algEquiv p q ε

example
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (ε : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    simpleMilnorNorm q
        (milnorKTransport ε.toRingHom n x : MilnorKRing (AdjoinRoot (poly q))) =
      simpleMilnorNorm p (x : MilnorKRing (AdjoinRoot (poly p))) :=
  simpleMilnorNorm_milnorKTransport_algEquiv p q ε n x

end
