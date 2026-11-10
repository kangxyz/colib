/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonSeparable

noncomputable section

open Polynomial Module IntermediateField Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (hb : Function.Bijective (algebraMap k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  let b : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L) hb
  let : Algebra.IsSeparable k L := AlgEquiv.Algebra.isSeparable b
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f x

example
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
  milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f x

example
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (f : L ≃ₐ[k] AdjoinRoot (poly p)) :
    milnorKNormRing k L =
      (simpleMilnorNorm p).comp (milnorKRingMap f.toRingHom).toAddMonoidHom :=
  milnorKNormRing_eq_comp_simpleMilnorNorm_of_algEquiv_of_isSeparable p f

example
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (f : L ≃ₐ[k] AdjoinRoot (poly p))
    (n : ℕ) (x : MilnorKTheory L n) :
    (milnorKNorm k L n x : MilnorKRing k) =
      simpleMilnorNorm p
        (milnorKTransport f.toRingHom n x : MilnorKRing (AdjoinRoot (poly p))) :=
  coe_milnorKNorm_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f n x

example
    {k : Type u} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    [FiniteDimensional k (AdjoinRoot (poly p))]
    [Algebra.IsSeparable k (AdjoinRoot (poly p))]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKNormRing k (AdjoinRoot (poly p)) x = simpleMilnorNorm p x :=
  milnorKNormRing_eq_simpleMilnorNorm_of_isSeparable p x

end
