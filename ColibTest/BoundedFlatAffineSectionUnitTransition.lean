/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionUnitNaturality

/-! Nontrivial-variable consumers of the actual section action and both evaluation routes. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.RegularSequence (globalSmulCenter)

noncomputable section

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt boundedAboveFlatPerfectGlobalUnitIso
  boundedAboveFlatAffineSectionsMap boundedAboveFlatAffineSectionUnitIso
universe u

variable (R : CommRingCat.{u}) (q : (Γ(Spec R, ⊤))ˣ)
  (s : BoundedAboveFlatAffineSections R) (j : Under R) (n : ℤ)

example :
    let φ : s ⟶ s := (boundedAboveFlatAffineSectionUnitIso R q).hom.app s
    (boundedAboveFlatPerfectPullback (Spec.map j.hom)).map
        ((boundedAboveFlatAffineOriginalEvaluation R).map φ) ≫
      (boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app s =
    (boundedAboveFlatAffineEvaluationPullbackIso R j).hom.app s ≫
      (boundedAboveFlatAffineEvaluationAt R j).map φ := by
  let φ : s ⟶ s := (boundedAboveFlatAffineSectionUnitIso R q).hom.app s
  exact boundedAboveFlatAffineEvaluationPullbackIso_naturality (s := s) (t := s) R φ j

