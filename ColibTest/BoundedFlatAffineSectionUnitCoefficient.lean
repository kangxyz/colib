/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit

/-! Nontrivial-variable consumers of the actual section action and both evaluation routes. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.RegularSequence (globalSmulCenter)

noncomputable section

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt boundedAboveFlatPerfectGlobalUnitIso
  boundedAboveFlatAffineSectionsMap boundedAboveFlatAffineSectionUnitIso
universe u

variable (R : CommRingCat.{u}) (q : (Γ(Spec R, ⊤))ˣ)
  (s : BoundedAboveFlatAffineSections R) (j : Under R) (n : ℤ)

variable {R} {S : CommRingCat.{u}} (f : R ⟶ S)

example :
    Functor.isoWhiskerRight (boundedAboveFlatAffineSectionUnitIso R q)
        (boundedAboveFlatAffineSectionsMap f) =
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom q)) :=
  boundedAboveFlatAffineSectionUnitIso_coefficient f q

example :
    Functor.whiskerRight (boundedAboveFlatAffineSectionUnitIso R q).inv
        (boundedAboveFlatAffineSectionsMap f) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom q)).inv :=
  boundedAboveFlatAffineSectionUnitIso_coefficient_inv f q

example :
    (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S).mapIso
        ((boundedAboveFlatAffineSectionUnitIso R q).app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec S)
        (Units.map (Spec.map f).appTop.hom.toMonoidHom q)).app
          ((boundedAboveFlatAffineSectionsMap f ⋙
            boundedAboveFlatAffineOriginalEvaluation S).obj s) := by
  rw [boundedAboveFlatAffineSectionsMap_comp_evaluation]
  exact boundedAboveFlatAffineEvaluationAt_mapIso_sectionUnitIso R q s (Under.mk f)

example (k : Under S) :
    (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineEvaluationAt S k).mapIso
        ((boundedAboveFlatAffineSectionUnitIso R q).app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec k.right)
        (Units.map (Spec.map ((Under.map f).obj k).hom).appTop.hom.toMonoidHom q)).app
          ((boundedAboveFlatAffineSectionsMap f ⋙
            boundedAboveFlatAffineEvaluationAt S k).obj s) := by
  rw [boundedAboveFlatAffineSectionsMap_comp_evaluationAt]
  exact boundedAboveFlatAffineEvaluationAt_mapIso_sectionUnitIso R q s ((Under.map f).obj k)

example :
    (boundedAboveFlatAffineEvaluationAt R (Under.mk (𝟙 R))).map
        ((boundedAboveFlatAffineSectionUnitIso R q).hom.app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec R) q).hom.app
        ((boundedAboveFlatAffineEvaluationAt R (Under.mk (𝟙 R))).obj s) := by
  rw [boundedAboveFlatAffineEvaluationAt_id]
  exact boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom R q s

example {i j : Under R} (a : i ⟶ j) :
    let φ : s ⟶ s := (boundedAboveFlatAffineSectionUnitIso R q).hom.app s
    s.obj.val.map a ≫ φ.hom.val.app j = φ.hom.val.app i ≫ s.obj.val.map a :=
  boundedAboveFlatAffineSectionUnitIso_section_naturality R q s a
