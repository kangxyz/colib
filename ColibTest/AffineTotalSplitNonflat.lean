/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompAssociation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Tactic.NormNum

/-! An actual quotient coefficient is accepted without any flatness input. -/
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u

noncomputable section

private def quotientCoefficient : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (Int.castRingHom (ZMod 2))

private theorem quotientRing_not_flat : ¬ (Int.castRingHom (ZMod 2)).Flat := by
  intro h
  have : Module.Flat ℤ (ZMod 2) := RingHom.flat_algebraMap_iff.mp h
  have hz : (2 : ℤ) = 0 ∨ (1 : ZMod 2) = 0 :=
    smul_eq_zero.mp (by decide : (2 : ℤ) • (1 : ZMod 2) = 0)
  exact one_ne_zero (hz.resolve_left (by norm_num))

example : ¬ AlgebraicGeometry.Flat (Spec.map quotientCoefficient) := by
  intro h
  exact quotientRing_not_flat (AlgebraicGeometry.Flat.SpecMap_iff.mp h)

example : ¬ Function.Injective (Int.castRingHom (ZMod 2)) := by
  intro h
  have hz : (2 : ℤ) = 0 := h (by decide)
  norm_num at hz

example :
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy quotientCoefficient
      (𝟙 (CommRingCat.of (ZMod 2)))).RelHomotopy
        (boundedAboveFlatAffineEvaluationCompSplitHomotopy quotientCoefficient
          (𝟙 (CommRingCat.of (ZMod 2)))) :=
  boundedAboveFlatAffineEvaluationCompTotalSplit quotientCoefficient _
