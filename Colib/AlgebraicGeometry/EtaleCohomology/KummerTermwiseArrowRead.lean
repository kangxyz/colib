/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExactExtendedTail

/-!
# Reading the actual original bounded coefficient arrow on complexes

Keep all three original bounded homotopy comparison factors. The proposed
identity must compile against their real definitions, not an asserted replacement.
Final coefficient/Ext assembly and degree-zero are not proved here.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Actual bounded homotopy arrow occurring after factorsh in the original coefficient map. -/
def kummerCoefficientBoundedArrow (M : EtaleModules.{u, 0} Λ X) :=
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ R))).hom.app K ≫
    (Functor.mapHomotopyCategoryPlusNatIso
      (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)).hom.app K ≫
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ H))).inv.app K

/-- The actual original three-factor bounded homotopy arrow, after the actual inclusion,
is the original coefficient natural transformation on the extended chosen complex. -/
theorem kummerCoefficientBoundedArrow_underlying (M : EtaleModules.{u, 0} Λ X) :
    (HomotopyCategory.Plus.ι (ModuleCat.{u + 1} ℤ)).map
      (kummerCoefficientBoundedArrow Λ X M) =
    (HomotopyCategory.quotient (ModuleCat.{u + 1} ℤ) (.up ℤ)).map
      (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.mapHomologicalComplex
        (.up ℤ)).app
        ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)) := by
  rfl

/-- Reading the original arrow in the derived category gives the same original
coefficient map on the extended chosen complex. -/
theorem kummerCoefficientBoundedArrow_derived (M : EtaleModules.{u, 0} Λ X) :
    DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (kummerCoefficientBoundedArrow Λ X M)) =
    DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat.{u + 1} ℤ) (.up ℤ)).map
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.mapHomologicalComplex
          (.up ℤ)).app
          ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) := by
  exact congrArg DerivedCategory.Qh.map (kummerCoefficientBoundedArrow_underlying Λ X M)

end Stacks.EtaleCohomology
end
