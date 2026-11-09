/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionWaldhausen

/-! Full-signature consumers for the actual fixed-open supported evaluation. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation
  boundedAboveFlatAffineSectionZero

example (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedEvaluation j).obj s).obj =
      ((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj).obj :=
  boundedAboveFlatAffineSupportedEvaluation_obj j s

/-- The literal forgetful composite retains both original objects and every original arrow. -/
private theorem lift_comp_inclusion {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty D) (F : C ⥤ D) (h : ∀ X, P (F.obj X)) :
    P.lift F h ⋙ P.ι = F := rfl

example : boundedAboveFlatAffineSupportedEvaluation j ⋙
      (boundedAboveFlatPerfectSupported j).ι =
    (boundedAboveFlatAffineSectionSupported j).ι ⋙ boundedAboveFlatAffineOriginalEvaluation R ⋙
      (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι := by
  unfold boundedAboveFlatAffineSupportedEvaluation
  exact lift_comp_inclusion _ _ _

example (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    (boundedAboveFlatAffineSupportedEvaluation j).obj
        ((boundedAboveFlatAffineSupportedSectionEquivalence j).inverse.obj K) ≅ K :=
  boundedAboveFlatAffineSupportedEvaluationCounit j K

example : (boundedAboveFlatAffineSupportedSectionZero j).obj = boundedAboveFlatAffineSectionZero R
  := rfl
example : IsZero (boundedAboveFlatAffineSupportedSectionZero j) :=
  isZero_boundedAboveFlatAffineSupportedSectionZero j
example : (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
  boundedAboveFlatAffineSupportedSectionZero j :=
  boundedAboveFlatAffineSupportedSectionWaldhausen_zero j
