/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalMiddleResolution

/-! # Original coefficient source normalization with all actual termwise factors retained -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma pasteNormalizedSource {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E H : C} {V W : D} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ H)
    (x : V ⟶ F.obj A) (r : V ⟶ W) (e : W ⟶ F.obj E)
    (h : x ≫ F.map (a ≫ b) = r ≫ e) :
    x ≫ F.map a ≫ F.map (b ≫ c) = r ≫ e ≫ F.map c := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg (· ≫ F.map c) h

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The original exact-derived and termwise coefficient factors, without the source unit. -/
def kummerCoefficientTermwiseArrow (M : EtaleModules.{u, 0} Λ X) :=
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  R.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ R))).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ H))).inv.app K)

set_option backward.isDefEq.respectTransparency false in
/-- Cancel the actual source augmentation/unit inside the original homology comparison;
all exact-derived and termwise coefficient factors are kept, not identified by fiat. -/
theorem kummerCoefficientPrefix_source_normalization
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    let A := G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)
    let B := DerivedCategory.Plus.Qh.obj
      (G.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj M))
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) A).inv ≫
      D.map (kummerCoefficientSourceAugmentation Λ X M) ≫
      D.map (kummerCoefficientResolutionPrefix Λ X M) =
    R.map (derivedPlusResolutionHomologyIso G (injectiveResolution M) q).hom ≫
      (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) B).inv ≫
      D.map (kummerCoefficientTermwiseArrow Λ X M) := by
  exact pasteNormalizedSource _ _ _ _ _ _ _
    (kummerExactCoefficientHomology_source_normalization Λ X M q)

end Stacks.EtaleCohomology
end
