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

-- Infer the full equality type from its actual identity-coefficient theorem application.
example := @boundedAboveFlatAffineSectionUnitIso_coefficient R R (𝟙 R) q
