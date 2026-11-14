/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors

/-!
# The original coefficient comparison on injective complexes

Compute the actual derived comparison through its unit. Restriction of an injective
complex is only asserted to be termwise acyclic, not injective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The source derived unit really is invertible on a bounded-below injective complex.
This is proved by termwise injectivity, not assumed as part of the comparison. -/
theorem kummerGlobalSectionsUnit_isIso
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ i : ℤ, Injective (K.obj.as.X i)) :
    IsIso ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlusUnith.app K) := by
  apply Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
  intro i
  have := hK i
  exact rightAcyclic_globalSections_of_isAcyclicEverywhere _
    (isAcyclicEverywhere_of_injective (K.obj.as.X i))

/-- Restricting the coefficients need not preserve injectives. It DOES make every
term acyclic for global sections, which suffices to invert the derived unit. -/
theorem kummerRestrictedGlobalSectionsUnit_isIso
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ i : ℤ, Injective (K.obj.as.X i)) :
    IsIso ((etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlusUnith.app
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapHomotopyCategoryPlus.obj K)) := by
  apply Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
  intro i
  have := hK i
  exact rightAcyclic_globalSections_of_isAcyclicEverywhere _
    (isAcyclicEverywhere_restrictScalars' (Int.castRingHom Λ) (K.obj.as.X i))

/-- Resolution-level value of the ORIGINAL derived coefficient comparison.
The right side is the termwise coefficient comparison and the actual derived unit
at the restricted complex. The restricted complex is not declared injective. -/
theorem kummerDerivedCoefficientComparison_on_injectiveComplex
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ i : ℤ, Injective (K.obj.as.X i)) :
    (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
        (DerivedCategory.Plus.Qh.obj K) =
    inv ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlusUnith.app K)) ≫
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlusFactorsh.hom.app
      ((etaleModuleGlobalSections.{u, 0} Λ X).mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (etaleModuleGlobalSections.{u, 0} Λ X ⋙
          ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)))).hom.app K ≫
       (Functor.mapHomotopyCategoryPlusNatIso
         (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)).hom.app K ≫
       (Functor.mapHomotopyCategoryPlusCompIso
         (Iso.refl (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙
           etaleModuleGlobalSections.{u, 0} ℤ X))).inv.app K) ≫
    (etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlusUnith.app
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapHomotopyCategoryPlus.obj K) ≫
    (etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlus.map
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlusFactorsh.inv.app K)
      := by
  let := kummerGlobalSectionsUnit_isIso Λ X K hK
  have h := Functor.map_unit_comp_rightDerivedRestrictionIso_hom_app
    (etaleModuleGlobalSections.{u, 0} Λ X)
    (etaleModuleGlobalSections.{u, 0} ℤ X)
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))
    (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)
    (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (isAcyclicEverywhere_restrictScalars' (Int.castRingHom Λ) I)) K
  have h' := congrArg (fun z =>
    inv ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlusUnith.app K)) ≫ z) h
  simpa only [IsIso.inv_hom_id_assoc, Category.assoc,
    etaleModuleDerivedGlobalSectionsRestrictScalars] using h'

end Stacks.EtaleCohomology
end
