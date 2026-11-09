module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTower

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x :=
  milnorKNormRing_map_algEquiv f x

example
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M] (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L :=
  milnorKNormRing_comp_map_algEquiv f

example
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x :=
  milnorKNorm_map_algEquiv f n x

example
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKNormRing M L x) = milnorKNormRing k L x :=
  milnorKNormRing_tower (k := k) (M := M) x

example
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRing k M).comp (milnorKNormRing M L) = milnorKNormRing k L :=
  milnorKNormRing_comp_milnorKNormRing (k := k) (M := M) (L := L)

example
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKNorm M L n x) = milnorKNorm k L n x :=
  milnorKNorm_tower (k := k) (M := M) n x

example
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    (milnorKNorm k M n).comp (milnorKNorm M L n) = milnorKNorm k L n :=
  milnorKNorm_comp_milnorKNorm (k := k) (M := M) (L := L) n

end
