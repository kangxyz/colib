/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceBoundaryCore

/-!
# The canonical Cartier difference on the whole boundary

The actual canonical difference section has coordinate one in the original native
boundary frame, including the full nonreduced boundary.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace Stacks.Divisors

variable {X B : Scheme.{u}} (i : B ⟶ X) (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

private theorem frame_canonicalDifferenceRegularSection_preimage_of_iso
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf)
    (he : e = differenceSheafBoundaryIsoOfComapEqTop i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE)) :
    e.hom.app (i ⁻¹ᵁ canonicalDifferenceRegularOpen E)
      (pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E)
        (i ⁻¹ᵁ canonicalDifferenceRegularOpen E) le_rfl
        (canonicalDifferenceRegularSection D E)) =
      (1 : Γ(B, i ⁻¹ᵁ canonicalDifferenceRegularOpen E)) := by
  exact (congrArg (fun f : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf => f.hom.app (i ⁻¹ᵁ canonicalDifferenceRegularOpen E)
        (pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E)
          (i ⁻¹ᵁ canonicalDifferenceRegularOpen E) le_rfl
          (canonicalDifferenceRegularSection D E))) he).trans
    (frame_canonicalDifferenceRegularSection_preimage i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE))

omit [IsEffectiveCartierDivisor D] in
private theorem frame_canonicalDifferenceBoundaryRegularSection_of_preimage
    (hE : ∀ y : B, i y ∉ E.support)
    (e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf)
    (ha : e.hom.app (i ⁻¹ᵁ canonicalDifferenceRegularOpen E)
      (pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E)
        (i ⁻¹ᵁ canonicalDifferenceRegularOpen E) le_rfl
        (canonicalDifferenceRegularSection D E)) =
      (1 : Γ(B, i ⁻¹ᵁ canonicalDifferenceRegularOpen E))) :
    e.hom.app ⊤ (canonicalDifferenceBoundaryRegularSection i D E hE) =
      (1 : Γ(B, ⊤)) := by
  refine (congrArg (e.hom.app ⊤)
    (canonicalDifferenceBoundaryRegularSection_eq_pullback i D E hE)).trans ?_
  exact frame_pullbackSectionHom_top_of_preimage i (differenceSheaf D E)
    (canonicalDifferenceRegularOpen E) e (canonicalDifferenceRegularSection D E)
    (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge ha

private theorem frame_canonicalDifferenceBoundaryRegularSection_eq_one_of_iso
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf)
    (he : e = differenceSheafBoundaryIsoOfComapEqTop i D E
      (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE)) :
    e.hom.app ⊤ (canonicalDifferenceBoundaryRegularSection i D E hE) =
      (1 : Γ(B, ⊤)) :=
  frame_canonicalDifferenceBoundaryRegularSection_of_preimage i D E hE e
    (frame_canonicalDifferenceRegularSection_preimage_of_iso i D E hD hE e he)

/-- The canonical meromorphic section's actual regular representative has coordinate
exactly one in the specified full-boundary frame. No reduction of the boundary is taken. -/
@[colib_tag "COL-1059",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/InvertibleSheafPullback.lean:202-207"
    "ingredient" "The native pullback comparison preserves the original canonical section",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/IdealSheafPullbackComap.lean:254-263"
    "ingredient" "The native original-ideal comparison preserves the ambient section",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/PullbackTensorTrivialization.lean:133-152"
    "ingredient" "The native tensor comparison transports original pure sections"]
theorem frame_canonicalDifferenceBoundaryRegularSection_eq_one
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support) :
    (differenceSheafBoundaryIso i D E hD hE).hom.app ⊤
      (canonicalDifferenceBoundaryRegularSection i D E hE) = (1 : Γ(B, ⊤)) := by
  exact frame_canonicalDifferenceBoundaryRegularSection_eq_one_of_iso i D E hD hE
    (differenceSheafBoundaryIso i D E hD hE)
    (differenceSheafBoundaryIso_eq_ofComap i D E hD hE)

end Stacks.Divisors
