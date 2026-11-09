/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphism

/-!
# Global units on actual bounded-flat cocartesian sections

The proved fully faithful original evaluation lifts the original global-unit automorphism to a
natural automorphism of actual cocartesian sections. Both its forward and inverse actions evaluate
to the unchanged geometric scalar maps; no scalar or section replacement is chosen.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original geometric unit acts on the actual cocartesian section category. -/
@[colib_tag "COL-0359",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
      SectionUnitAction.lean:28-31"
    "adaptation" "Global units lifted through fully faithful native section evaluation"]
def boundedAboveFlatAffineSectionUnitIso (R : CommRingCat.{u}) (r : (Γ(Spec R, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatAffineSections R) ≅ 𝟭 (BoundedAboveFlatAffineSections R) :=
  Functor.IdentityAutomorphism.lift (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r)

private theorem sectionUnitIso_eq (R : CommRingCat.{u}) (r : (Γ(Spec R, ⊤))ˣ) :
    boundedAboveFlatAffineSectionUnitIso R r =
      Functor.IdentityAutomorphism.lift (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r) := rfl

/-- Original evaluation retains the actual geometric unit action on every section. -/
theorem boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineOriginalEvaluation R).map
        ((boundedAboveFlatAffineSectionUnitIso R r).hom.app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r).hom.app
        ((boundedAboveFlatAffineOriginalEvaluation R).obj s) := by
  rw [sectionUnitIso_eq]
  exact Functor.IdentityAutomorphism.map_lift_hom (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r) s

/-- Original evaluation retains multiplication by the inverse original unit as well. -/
theorem boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_inv (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineOriginalEvaluation R).map
        ((boundedAboveFlatAffineSectionUnitIso R r).inv.app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r).inv.app
        ((boundedAboveFlatAffineOriginalEvaluation R).obj s) := by
  rw [sectionUnitIso_eq]
  exact Functor.IdentityAutomorphism.map_lift_inv (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectGlobalUnitIso (Spec R) r) s

end AlgebraicGeometry.Scheme.Modules
