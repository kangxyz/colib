/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! Actual nonflat reduction modulo two acts on relative K-theory and the original quotient. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
attribute [local instance] Abelian.hasFiniteBiproducts

private def reduction : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (algebraMap ℤ (ZMod 2))

private theorem reduction_not_flat : ¬ Flat (Spec.map reduction) := by
  intro h
  have hr := Flat.SpecMap_iff.mp h
  have : Module.Flat ℤ (ZMod 2) := RingHom.flat_algebraMap_iff.mp hr
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have he := smul_eq_zero.mp hz
  norm_num at he

private def sourcePair : Scheme.OpenPairs :=
  MorphismProperty.Arrow.mk (⊥ : (Spec (CommRingCat.of (ZMod 2))).Opens).ι inferInstance

private def targetPair : Scheme.OpenPairs :=
  MorphismProperty.Arrow.mk (𝟙 (Spec (CommRingCat.of ℤ))) inferInstance

private def reductionPair : sourcePair ⟶ targetPair :=
  MorphismProperty.Arrow.homMk (sourcePair.hom ≫ Spec.map reduction) (Spec.map reduction)
    (by change (sourcePair.hom ≫ Spec.map reduction) ≫ 𝟙 _ =
        sourcePair.hom ≫ Spec.map reduction; simp)

example : ¬ Flat reductionPair.right := reduction_not_flat

example (n : ℕ) :
    BoundedAboveFlatPerfectOpenK targetPair.hom n →*
      BoundedAboveFlatPerfectOpenK sourcePair.hom n :=
  boundedAboveFlatPerfectOpenKPullback reductionPair n

example :
    boundedAboveFlatPerfectOpenKPullback reductionPair 0 =
      KMap (boundedAboveFlatPerfectOpenPullback_isExact reductionPair) 0 := rfl

example
    (Q : ShortComplex
      (boundedAboveFlatPerfectComplex targetPair.right.toRingedSpace).FullSubcategory)
    (hQ : (Q.map (boundedAboveFlatPerfectComplex targetPair.right.toRingedSpace).ι).ShortExact) :
    ((Q.map (boundedAboveFlatPerfectPullback reductionPair.right)).map
      (boundedAboveFlatPerfectComplex sourcePair.right.toRingedSpace).ι).ShortExact :=
  (boundedAboveFlatPerfectExactPullback reductionPair.right).map_conflation Q hQ

example
    (Q : ShortComplex
      (boundedAboveFlatPerfectComplex targetPair.right.toRingedSpace).FullSubcategory) :
    ((Q.map (boundedAboveFlatPerfectPullback reductionPair.right)).X₃).obj =
      (((Scheme.Modules.pullback reductionPair.right).mapHomologicalComplex (.up ℤ)).obj
        Q.X₃.obj) := rfl
