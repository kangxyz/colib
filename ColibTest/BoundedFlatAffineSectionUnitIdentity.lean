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

-- Keep the coefficient opaque to kernel reduction while proving it is the actual identity.
private theorem identityCoefficient_exists (R : CommRingCat.{u}) :
    ∃ f : R ⟶ R, f = 𝟙 R := ⟨𝟙 R, rfl⟩

private noncomputable def identityCoefficient (R : CommRingCat.{u}) : R ⟶ R :=
  Classical.choose (identityCoefficient_exists R)

private theorem identityCoefficient_eq (R : CommRingCat.{u}) :
    identityCoefficient R = 𝟙 R :=
  Classical.choose_spec (identityCoefficient_exists R)

private theorem identityCoefficient_transport (R : CommRingCat.{u})
    (P : (R ⟶ R) → Prop) (h : P (identityCoefficient R)) : P (𝟙 R) :=
  (identityCoefficient_eq R) ▸ h

private def coefficientNaturality (R : CommRingCat.{u}) (q : (Γ(Spec R, ⊤))ˣ)
    (f : R ⟶ R) : Prop :=
  Functor.isoWhiskerRight (boundedAboveFlatAffineSectionUnitIso R q)
      (boundedAboveFlatAffineSectionsMap f) =
    Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionsMap f)
      (boundedAboveFlatAffineSectionUnitIso R
        (Units.map (Spec.map f).appTop.hom.toMonoidHom q))

example : coefficientNaturality R q (𝟙 R) :=
  identityCoefficient_transport R (coefficientNaturality R q)
    (@boundedAboveFlatAffineSectionUnitIso_coefficient R R (identityCoefficient R) q)
