/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerResolutionUnitTransport

/-!
# The original coefficient comparison on two actual resolutions

Paste actual derived units and the constructed restricted resolution comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma pasteResolution {A : Type*} [Category* A]
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ : A}
    {a : V₀ ⟶ V₁} {b : V₁ ⟶ V₂} {c : V₂ ⟶ V₃} {d : V₃ ⟶ V₄}
    (e : V₅ ≅ V₄) {f : V₄ ⟶ V₆} {g : V₆ ⟶ V₇} {r : V₃ ⟶ V₇}
    {cmp : V₀ ⟶ V₅} (hc : cmp = a ≫ b ≫ c ≫ d ≫ e.inv)
    (hu : d ≫ f ≫ g = r) :
    cmp ≫ e.hom ≫ f ≫ g = a ≫ b ≫ c ≫ r := by
  rw [hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hu]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Source unit, proved invertible on the actual chosen injective resolution. -/
def kummerCoefficientResolutionSourceIso (M : EtaleModules.{u, 0} Λ X) :=
  have := kummerGlobalSectionsUnit_isIso Λ X (Stacks.DerivedIndexing.resPlus.obj M)
    (fun _ => inferInstance)
  asIso ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
    ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlusUnith.app
      (Stacks.DerivedIndexing.resPlus.obj M)))

/-- The original derived coefficient comparison followed by actual chosen-resolution
transport is computed by the original termwise comparison and the actual complex map. -/
theorem kummerCoefficientComparison_on_chosen_resolutions (M : EtaleModules.{u, 0} Λ X) :
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
        (DerivedCategory.Plus.Qh.obj K) ≫
      H.rightDerivedFunctorPlus.map (T.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      H.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M)) ≫
      (kummerRestrictedTargetUnitIso Λ X M).inv =
    (kummerCoefficientResolutionSourceIso Λ X M).inv ≫
      R.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ R))).hom.app K ≫
          (Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)).hom.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ H))).inv.app K) ≫
      DerivedCategory.Plus.Qh.map
        (H.mapHomotopyCategoryPlus.map (kummerRestrictedResolutionPlus Λ X M)) := by
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  have hc := kummerDerivedCoefficientComparison_on_injectiveComplex Λ X K
    (fun _ => inferInstance)
  have hu := kummerRestrictedResolution_unit_cancel Λ X M
  exact pasteResolution (H.rightDerivedFunctorPlus.mapIso
    (T.mapDerivedCategoryPlusFactorsh.app K)) hc hu

end Stacks.EtaleCohomology
end
