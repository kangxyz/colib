/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTower

/-!
# Arbitrary simple first steps of the native chosen Milnor norm

The native chosen norm on the actual intermediate field `K⟮a⟯` equals
`milnorKNormAdjoinSimple`, by its native minimal-polynomial presentation.
Transitivity then permits any element as the first step, including elements of
the base field. Two choices give the same composite on the original source.
All scalar actions and the common universe are unchanged; no norm is redefined.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u

namespace Stacks.Chow

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The chosen norm on the actual simple adjoin equals its native simple norm. -/
theorem milnorKNormRing_adjoinSimple_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    {a : L} (h : IsIntegral K a) [FiniteDimensional K K⟮a⟯]
    (x : MilnorKRing K⟮a⟯) :
    milnorKNormRing K K⟮a⟯ x = milnorKNormAdjoinSimple K h x := by
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv
    (minpolyOfDegree K h) (adjoinSimpleEquivQuot K h) x

/-- Equality of the original additive maps on the actual simple adjoin. -/
theorem milnorKNormRing_adjoinSimple
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    {a : L} (h : IsIntegral K a) [FiniteDimensional K K⟮a⟯] :
    milnorKNormRing K K⟮a⟯ = milnorKNormAdjoinSimple K h := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRing_adjoinSimple_apply h x

/-- Any element gives a first-step formula for the original finite chosen norm. -/
theorem milnorKNormRing_adjoinSimple_step_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNormRing K⟮a⟯ L x) = milnorKNormRing K L x := by
  rw [← milnorKNormRing_adjoinSimple]
  exact milnorKNormRing_tower (k := K) (M := K⟮a⟯) x

/-- First-step recursion as equality of the original additive maps, for any element. -/
theorem milnorKNormRing_adjoinSimple_step
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) :
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)).comp
      (milnorKNormRing K⟮a⟯ L) = milnorKNormRing K L := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRing_adjoinSimple_step_apply a x

/-- The composites for any two simple first steps agree pointwise. -/
theorem milnorKNormRing_adjoinSimple_choice_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a b : L) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNormRing K⟮a⟯ L x) =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) b)
        (milnorKNormRing K⟮b⟯ L x) := by
  exact (milnorKNormRing_adjoinSimple_step_apply a x).trans
    (milnorKNormRing_adjoinSimple_step_apply b x).symm

/-- Any two choices give the same original additive composite, including base elements. -/
theorem milnorKNormRing_adjoinSimple_choice
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a b : L) :
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)).comp
        (milnorKNormRing K⟮a⟯ L) =
      (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) b)).comp
        (milnorKNormRing K⟮b⟯ L) := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRing_adjoinSimple_choice_apply a b x

/-- The arbitrary first-step formula on each homogeneous degree, in the native ring. -/
theorem coe_milnorKNorm_adjoinSimple_step
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNorm K⟮a⟯ L n x : MilnorKRing K⟮a⟯) =
      (milnorKNorm K L n x : MilnorKRing K) := by
  exact milnorKNormRing_adjoinSimple_step_apply a (x : MilnorKRing L)

end Stacks.Chow

end
