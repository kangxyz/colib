/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! A concrete nonflat affine morphism still preserves the original admissible quotient. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts

private def reduction : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (algebraMap ℤ (ZMod 2))

private theorem reduction_not_flat : ¬ Flat (Spec.map reduction) := by
  intro h
  have hr := Flat.SpecMap_iff.mp h
  have : Module.Flat ℤ (ZMod 2) := RingHom.flat_algebraMap_iff.mp hr
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have he := (smul_eq_zero.mp hz)
  norm_num at he

private def sourcePair : Scheme.OpenPairs :=
  MorphismProperty.Arrow.mk (𝟙 (Spec (CommRingCat.of (ZMod 2)))) inferInstance

private def targetPair : Scheme.OpenPairs :=
  MorphismProperty.Arrow.mk (𝟙 (Spec (CommRingCat.of ℤ))) inferInstance

private def reductionPair : sourcePair ⟶ targetPair :=
  MorphismProperty.Arrow.homMk (Spec.map reduction) (Spec.map reduction)
    (by change Spec.map reduction ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map reduction; simp)

example : ¬ Flat reductionPair.right := reduction_not_flat

example (Q : ShortComplex (boundedAboveFlatPerfectSupported targetPair.hom).FullSubcategory)
    (hQ : (Q.map (boundedAboveFlatPerfectSupported targetPair.hom).ι).ShortExact) :
    ((Q.map (boundedAboveFlatPerfectSupportedPullback reductionPair)).map
      (boundedAboveFlatPerfectSupported sourcePair.hom).ι).ShortExact :=
  (boundedAboveFlatPerfectSupportedExactPullback reductionPair).map_conflation Q hQ

example (Q : ShortComplex (boundedAboveFlatPerfectSupported targetPair.hom).FullSubcategory) :
    ((Q.map (boundedAboveFlatPerfectSupportedPullback reductionPair)).X₃).obj =
      (((Scheme.Modules.pullback reductionPair.right).mapHomologicalComplex (.up ℤ)).obj
        Q.X₃.obj) :=
  rfl
