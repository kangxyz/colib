/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionZero
public import Colib.CategoryTheory.Waldhausen.EquivalenceStructure

/-!
# Genuine Waldhausen structure on original supported affine sections

The proved original supported evaluation equivalence transports the original geometric
cofibrations, weak equivalences and pushouts. The chosen zero is the same source-independent
supported section proved earlier. Both directions of that actual equivalence are exact.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation


private theorem equivalence_obj_isZero {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) {X : C} (hX : IsZero X) : IsZero (e.functor.obj X) :=
  IsZero.of_full_of_faithful_of_isZero e.inverse _ (hX.of_iso (e.unitIso.app X).symm)

/-- Actual supported evaluation carries the original chosen section to a genuine zero object. -/
theorem boundedAboveFlatAffineSupportedEvaluation_sectionZero_isZero :
    IsZero ((boundedAboveFlatAffineSupportedEvaluation j).obj
      (boundedAboveFlatAffineSupportedSectionZero j)) := by
  rw [← boundedAboveFlatAffineSupportedSectionEquivalence_functor]
  exact equivalence_obj_isZero (boundedAboveFlatAffineSupportedSectionEquivalence j)
    (isZero_boundedAboveFlatAffineSupportedSectionZero j)

/-- Original supported morphism classes and pushouts, with the unchanged chosen zero section. -/
def boundedAboveFlatAffineSupportedSectionWaldhausen :
    Waldhausen.Structure (BoundedAboveFlatAffineSupportedSections j) :=
  (boundedAboveFlatPerfectSupportedWaldhausen j).ofEquivalence
    (boundedAboveFlatAffineSupportedSectionEquivalence j)
      (boundedAboveFlatAffineSupportedSectionZero j)
    (by rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]
        exact boundedAboveFlatAffineSupportedEvaluation_sectionZero_isZero j)

/-- The chosen zero retains the exact original supported section. -/
theorem boundedAboveFlatAffineSupportedSectionWaldhausen_zero :
    (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
      boundedAboveFlatAffineSupportedSectionZero j := rfl

/-- Cofibrations are precisely the original geometric supported cofibrations under evaluation. -/
theorem boundedAboveFlatAffineSupportedSectionWaldhausen_cof_iff
    {X Y : BoundedAboveFlatAffineSupportedSections j} (f : X ⟶ Y) :
    (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof f ↔
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
        ((boundedAboveFlatAffineSupportedEvaluation j).map f) := by
  change (boundedAboveFlatPerfectSupportedWaldhausen j).cof
    ((boundedAboveFlatAffineSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]

/-- Weak equivalences are the original geometric supported weak maps under evaluation. -/
theorem boundedAboveFlatAffineSupportedSectionWaldhausen_weq_iff
    {X Y : BoundedAboveFlatAffineSupportedSections j} (f : X ⟶ Y) :
    (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq f ↔
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
        ((boundedAboveFlatAffineSupportedEvaluation j).map f) := by
  change (boundedAboveFlatPerfectSupportedWaldhausen j).weq
    ((boundedAboveFlatAffineSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]

/-- The original supported evaluation is exact for these genuinely constructed structures. -/
theorem boundedAboveFlatAffineSupportedEvaluation_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof (boundedAboveFlatPerfectSupportedWaldhausen
        j).weq
      (boundedAboveFlatAffineSupportedEvaluation j) := by
  rw [← boundedAboveFlatAffineSupportedSectionEquivalence_functor]
  exact Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- The same actual supported inverse equivalence is also Waldhausen-exact. -/
theorem boundedAboveFlatAffineSupportedSectionEquivalence_inverse_exact :
    Waldhausen.IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionEquivalence j).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

end AlgebraicGeometry.Scheme.Modules
