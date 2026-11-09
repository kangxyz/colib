/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.CategoryTheory.FiberedCategory.GrothendieckZeroSections

/-!
# Source-independent pointwise chosen-zero sections

Adapted from the corresponding bounded-flat section constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native geometric objects and structures.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckZeroSections
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original chosen zero family, independent of any source ring. -/
def boundedAboveFlatAffineChosenZero (S : CommRingCat.{u}) :
    boundedAboveFlatAffinePseudofunctor.obj ⟨S⟩ :=
  (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).zero

/-- The existing chosen objects retain their actual zero universal properties. -/
theorem boundedAboveFlatAffineChosenZero_isZero (S : CommRingCat.{u}) :
    IsZero (boundedAboveFlatAffineChosenZero S) :=
  (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).isZero

/-- Actual exact pullback preserves the chosen zero's universal property. -/
theorem boundedAboveFlatAffineChosenZero_map_isZero {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsZero ((boundedAboveFlatAffinePseudofunctor.map f.toLoc).toFunctor.obj
      (boundedAboveFlatAffineChosenZero R)) :=
  (boundedAboveFlatPerfectPullback_isExact (Spec.map f)).zero
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero

/-- The chosen zero section uses the original bounded-flat zeros in every fiber. -/
def boundedAboveFlatAffineSectionZero (R : CommRingCat.{u}) : BoundedAboveFlatAffineSections R :=
  sectionZero boundedAboveFlatAffinePseudofunctor boundedAboveFlatAffineChosenZero
    boundedAboveFlatAffineChosenZero_isZero
    (fun {_ _} f => boundedAboveFlatAffineChosenZero_map_isZero f) R

/-- The specified pointwise zero section really is a zero object. -/
theorem isZero_boundedAboveFlatAffineSectionZero (R : CommRingCat.{u}) :
    IsZero (boundedAboveFlatAffineSectionZero R) :=
  isZero_sectionZero boundedAboveFlatAffinePseudofunctor boundedAboveFlatAffineChosenZero
    boundedAboveFlatAffineChosenZero_isZero
    (fun {_ _} f => boundedAboveFlatAffineChosenZero_map_isZero f) R

/-- Original evaluation retains the existing Waldhausen zero literally. -/
theorem boundedAboveFlatAffineOriginalEvaluation_sectionZero (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineOriginalEvaluation R).obj (boundedAboveFlatAffineSectionZero R) =
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero :=
  originalEvaluation_sectionZero boundedAboveFlatAffinePseudofunctor
    boundedAboveFlatAffineChosenZero
    boundedAboveFlatAffineChosenZero_isZero
    (fun {_ _} f => boundedAboveFlatAffineChosenZero_map_isZero f) R

/-- Strict coefficient restriction retains the chosen zero section literally. -/
theorem boundedAboveFlatAffineSectionsMap_sectionZero {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionsMap f).obj (boundedAboveFlatAffineSectionZero R) =
      boundedAboveFlatAffineSectionZero S :=
  reindex_sectionZero boundedAboveFlatAffinePseudofunctor boundedAboveFlatAffineChosenZero
    boundedAboveFlatAffineChosenZero_isZero
    (fun {_ _} f => boundedAboveFlatAffineChosenZero_map_isZero f) f

/-- Every coefficient-arrow evaluation retains the same target chosen zero literally. -/
theorem boundedAboveFlatAffineEvaluationAt_sectionZero (R : CommRingCat.{u}) (j : Under R) :
    (boundedAboveFlatAffineEvaluationAt R j).obj (boundedAboveFlatAffineSectionZero R) =
      (boundedAboveFlatPerfectWaldhausen (Spec j.right).toRingedSpace).zero := rfl

end AlgebraicGeometry.Scheme.Modules
