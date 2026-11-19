/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusIntegralUnderlying
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal

/-! # Ordinary integral tensor and smooth étale sheafification

This is the localization tensor on module-valued sheaves on the actual smooth site.
It does not assert preservation of K-flatness or a derived tensor comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
open CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalClosed

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Ordinary integral presheaves on the actual smooth site. -/
abbrev SmoothEtaleIntegralPresheaves :=
  (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ

/-- Ordinary integral sheaves for the actual smooth étale topology. -/
abbrev SmoothEtaleIntegralSheaves :=
  Sheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)

/-- The original integral sheafification, retained in public comparison types. -/
abbrev smoothEtaleIntegralSheafify :=
  presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)

/-- The original fully faithful inclusion of integral sheaves. -/
abbrev smoothEtaleIntegralInclusion :=
  sheafToPresheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)

/-- Local isomorphisms on the actual smooth étale site form a monoidal class. -/
theorem smoothEtaleIntegral_isMonoidal_W :
    ((SmoothSite.etaleTopology (Spec (CommRingCat.of k))).W
      (A := ModuleCat.{u + 1} ℤ)).IsMonoidal := by
  let _ : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} ℤ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0} (R := ℤ)
  let _ : EnrichedOrdinaryCategory (ModuleCat.{u + 1} ℤ)
      (ModuleCat.{u + 1} ℤ) := inferInstance
  let _ : ∀ P Q : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ,
      HasFunctorEnrichedHom (ModuleCat.{u + 1} ℤ) P Q := by
    intro P Q V
    infer_instance
  let _ : ∀ P Q : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ,
      HasEnrichedHom (ModuleCat.{u + 1} ℤ) P Q := by
    intro P Q
    infer_instance
  exact GrothendieckTopology.W.monoidal

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory

/-- The ordinary tensorator of the original smooth étale sheafification. -/
def smoothEtaleIntegralTensorIso
    (P Q : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :
    (presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{u + 1} ℤ)).obj (P ⊗ Q) ≅
    (presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{u + 1} ℤ)).obj P ⊗
    (presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{u + 1} ℤ)).obj Q :=
  (Functor.Monoidal.μIso
    (presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{u + 1} ℤ)) P Q).symm

end AlgebraicGeometry.PresheafWithTransfers
