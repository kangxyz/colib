/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIntegralCocycleRead

/-!
# Original coefficient-derived map on the actual resolution homology

Retain actual derived units and coefficient factors. Evaluate the chosen
resolution map via the previously verified extended-homology comparison. This is a
resolution-level statement; transport from the original single object remains separate.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma mapAndPaste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' E G : C} {a : A ⟶ B} {b : B ⟶ C'} {c : C' ⟶ E} {d : E ⟶ G}
    {x : A ⟶ G} {V W : D} {e : F.obj G ⟶ W} {f : F.obj E ⟶ V} {g : V ⟶ W}
    (hx : x = a ≫ b ≫ c ≫ d) (hd : F.map d ≫ e = f ≫ g) :
    F.map x ≫ e = F.map (a ≫ b ≫ c) ≫ f ≫ g := by
  simp only [hx, Functor.map_comp, Category.assoc]
  rw [hd]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Original coefficient-derived map at the actual chosen resolution, followed by
actual resolution transport and inverse actual target unit. -/
def kummerCoefficientResolutionLeft (M : EtaleModules.{u, 0} Λ X) :=
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
      (DerivedCategory.Plus.Qh.obj K) ≫
    H.rightDerivedFunctorPlus.map (T.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    H.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M)) ≫
    (kummerRestrictedTargetUnitIso Λ X M).inv

/-- Actual original source-unit and coefficient factors before the chosen complex map. -/
def kummerCoefficientResolutionPrefix (M : EtaleModules.{u, 0} Λ X) :=
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  (kummerCoefficientResolutionSourceIso Λ X M).inv ≫
    R.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ R))).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ H))).inv.app K)

/-- The ORIGINAL resolution-level coefficient comparison becomes the actual ordinary
homology map of the chosen comparison, with all source factors retained. -/
theorem kummerCoefficientResolution_homology (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    D.map (kummerCoefficientResolutionLeft Λ X M) ≫
      (extendedHomologyIso H (injectiveResolution (T.obj M)).cocomplex q).hom =
    D.map (kummerCoefficientResolutionPrefix Λ X M) ≫
      (extendedHomologyIso (T ⋙ H) (injectiveResolution M).cocomplex q).hom ≫
      HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (kummerRestrictedResolutionComparison Λ X M)) q := by
  exact mapAndPaste
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ))
    (kummerCoefficientComparison_on_chosen_resolutions Λ X M)
    (kummerRestrictedResolution_homology Λ X M q)

end Stacks.EtaleCohomology
end
