/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenDiagram
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.NormNum

/-! A proved nonflat reduction acts across a noncartesian open square and composes literally. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.AffineOpenPair

private def reduction : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (algebraMap ℤ (ZMod 2))

private theorem reduction_not_flat : ¬ Flat (Spec.map reduction) := by
  intro h
  have hr := Flat.SpecMap_iff.mp h
  have : Module.Flat ℤ (ZMod 2) := RingHom.flat_algebraMap_iff.mp hr
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have he := smul_eq_zero.mp hz
  norm_num at he

private abbrev emptyInclusion := (⊥ : (Spec (CommRingCat.of (ZMod 2))).Opens).ι

private theorem empty_square :
    (emptyInclusion ≫ Spec.map reduction) ≫ 𝟙 (Spec (CommRingCat.of ℤ)) =
      emptyInclusion ≫ Spec.map reduction := by simp

private theorem empty_square_not_cartesian :
    ¬ IsPullback (emptyInclusion ≫ Spec.map reduction) emptyInclusion
      (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map reduction) := by
  intro h
  have : IsIso emptyInclusion := h.isIso_snd_of_isIso
  let x : Spec (CommRingCat.of (ZMod 2)) := Classical.choice inferInstance
  exact ((inv emptyInclusion).base x).property

example : ¬ Flat (Spec.map reduction) := reduction_not_flat

example : ¬ IsPullback (emptyInclusion ≫ Spec.map reduction) emptyInclusion
    (𝟙 (Spec (CommRingCat.of ℤ))) (Spec.map reduction) := empty_square_not_cartesian

example :
    boundedAboveFlatAffineSectionOpenModel (𝟙 (Spec (CommRingCat.of ℤ))) ⟶
      boundedAboveFlatAffineSectionOpenModel emptyInclusion :=
  boundedAboveFlatAffineSectionOpenReindexModelMap _ _ reduction
    (emptyInclusion ≫ Spec.map reduction) empty_square

private def polynomialCoefficient :
    CommRingCat.of (ZMod 2) ⟶ CommRingCat.of (Polynomial (ZMod 2)) :=
  CommRingCat.ofHom Polynomial.C

private def reductionUnder : Under.mk (𝟙 (CommRingCat.of ℤ)) ⟶ Under.mk reduction :=
  Under.homMk reduction (by simp)

private def polynomialUnder : Under.mk reduction ⟶ Under.mk (reduction ≫ polynomialCoefficient) :=
  Under.homMk polynomialCoefficient rfl

example {U : Scheme} (j : U ⟶ Spec (CommRingCat.of ℤ)) [IsOpenImmersion j] :
    (boundedAboveFlatAffineSectionOpenModelFunctor j).map
        (reductionUnder ≫ polynomialUnder) =
      (boundedAboveFlatAffineSectionOpenModelFunctor j).map reductionUnder ≫
        (boundedAboveFlatAffineSectionOpenModelFunctor j).map polynomialUnder :=
  (boundedAboveFlatAffineSectionOpenModelFunctor j).map_comp reductionUnder polynomialUnder

example {U : Scheme} (j : U ⟶ Spec (CommRingCat.of ℤ)) [IsOpenImmersion j] :
    (((boundedAboveFlatAffineSectionOpenModelFunctor j).map reductionUnder).hom.toFunctor) =
      boundedAboveFlatAffineSectionsMap reduction := rfl
