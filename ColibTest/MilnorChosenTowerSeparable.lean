/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x :=
  milnorKNormRing_map_algEquiv_of_isSeparable f x

example
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M] (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L :=
  milnorKNormRing_comp_map_algEquiv_of_isSeparable f

example
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x :=
  milnorKNorm_map_algEquiv_of_isSeparable f n x

example
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKNormRing M L x) = milnorKNormRing k L x :=
  milnorKNormRing_tower_of_isSeparable (k := k) (M := M) x

example
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRing k M).comp (milnorKNormRing M L) = milnorKNormRing k L :=
  milnorKNormRing_comp_milnorKNormRing_of_isSeparable (k := k) (M := M) (L := L)

example
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKNorm M L n x) = milnorKNorm k L n x :=
  milnorKNorm_tower_of_isSeparable (k := k) (M := M) n x

example
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    (milnorKNorm k M n).comp (milnorKNorm M L n) = milnorKNorm k L n :=
  milnorKNorm_comp_milnorKNorm_of_isSeparable (k := k) (M := M) (L := L) n

end
