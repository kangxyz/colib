/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerResolutionModel

/-!
# Transport through the actual restricted resolution comparison

Cancel the genuine target resolution unit, not an assumed coefficient comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma cancelTargetUnit {A : Type*} [Category* A]
    {V₀ V₁ V₂ V₃ : A} (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₃)
    (c : V₀ ⟶ V₂) (d : V₂ ⟶ V₃) [IsIso d] (h : c ≫ d = a ≫ b) :
    a ≫ b ≫ inv d = c := by
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The actual unit on the chosen integral injective resolution is invertible. -/
theorem kummerRestrictedTargetUnit_isIso (M : EtaleModules.{u, 0} Λ X) :
    IsIso ((etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (EtaleModules.{u, 0} ℤ X)).obj
        (resolutionCochainPlus (injectiveResolution
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))))) := by
  apply kummerGlobalSectionsUnit_isIso
  intro i
  exact resolutionCochainPlus_injective _ i

/-- The target unit as the isomorphism supplied by actual injectivity. -/
def kummerRestrictedTargetUnitIso (M : EtaleModules.{u, 0} Λ X) :=
  have := kummerRestrictedTargetUnit_isIso Λ X M
  asIso ((etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient (EtaleModules.{u, 0} ℤ X)).obj
      (resolutionCochainPlus (injectiveResolution
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)))))

/-- Transporting along the actual comparison and cancelling the target unit computes
exactly the map of complexes induced on integral global sections. -/
theorem kummerRestrictedResolution_unit_cancel (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let G := etaleModuleGlobalSections.{u, 0} ℤ X
    let K := Stacks.DerivedIndexing.resPlus.obj M
    G.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M)) ≫
      (kummerRestrictedTargetUnitIso Λ X M).inv =
    DerivedCategory.Plus.Qh.map
      (G.mapHomotopyCategoryPlus.map (kummerRestrictedResolutionPlus Λ X M)) := by
  have := kummerRestrictedTargetUnit_isIso Λ X M
  exact cancelTargetUnit _ _ _ _ (kummerRestrictedResolutionPlus_unit Λ X M)

end Stacks.EtaleCohomology
end
