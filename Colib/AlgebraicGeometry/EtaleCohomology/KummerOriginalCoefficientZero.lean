/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerTermwiseExtendedAssembly
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionFormulaInDegreeZero

/-! # Degree-zero normalization of the original coefficient comparison

Read the actual comparison on the actual chosen resolutions.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma pasteCycles {C : Type*} [Category C]
    {A B D E F G H : C} (i : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E)
    (l : E ⟶ F) (k : D ⟶ G) (p : G ⟶ F) (j : B ⟶ H) (q : H ⟶ G)
    (r : A ⟶ H) (h₁ : v ≫ l = k ≫ p) (h₂ : u ≫ k = j ≫ q)
    (h₃ : i ≫ j = r) : (i ≫ u ≫ v) ≫ l = r ≫ q ≫ p := by
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc u k, h₂, Category.assoc, ← Category.assoc i j, h₃]

private lemma normalizationRead {C : Type*} [Category C] {A B D E : C}
    (p : A ⟶ B) (i : B ≅ D) (j : B ≅ E) (n : D ⟶ E) (a : A ⟶ E)
    (hi : i.inv ≫ j.hom = n) (hp : p = a ≫ j.inv) :
    (p ≫ i.hom) ≫ n = a := by
  rw [← hi, hp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient comparison in degree zero intertwines the canonical maps
from ordinary global sections into the original bounded-below derived global sections. -/
theorem kummerOriginalCoefficient_zero_normalization (M : EtaleModules.{u, 0} Λ X) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    R.map (G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M) ≫
      (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom =
    (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app M ≫
      H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M) := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let N := derivedPlusResolutionHomologyIso G I 0 ≪≫ extendedHomologyIso G I.cocomplex 0
  let P := derivedPlusResolutionHomologyIso H J 0 ≪≫ extendedHomologyIso H J.cocomplex 0
  let c := (mapExactCyclesIso R K 0).inv ≫ cyclesMap a 0 ≫ cyclesMap b 0
  let f := (mapExactHomologyIso R K 0).inv ≫ homologyMap a 0 ≫ homologyMap b 0
  have hc : c ≫ L.iCycles 0 =
      R.map (K.iCycles 0) ≫ e.hom.app (I.cocomplex.X 0) ≫ H.map (φ.f 0) := by
    have he := mapExactCyclesIso_hom_iCycles R K 0
    have he' : (mapExactCyclesIso R K 0).inv ≫
        ((R.mapHomologicalComplex (.up ℕ)).obj K).iCycles 0 = R.map (K.iCycles 0) := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact pasteCycles _ _ _ _ _ _ _ _ _ (cyclesMap_i b 0) (cyclesMap_i a 0) he'
  have hz := rightDerivedZeroCompForgetIso_cycles G R T H e I J φ
    (kummerRestrictedResolutionComparison_augmentation Λ X M) c hc
  have hπ : R.map (K.homologyπ 0) ≫ f = c ≫ L.homologyπ 0 := by
    have he := homologyπ_mapExactHomologyIso_hom R K 0
    have he' : R.map (K.homologyπ 0) ≫ (mapExactHomologyIso R K 0).inv =
        (mapExactCyclesIso R K 0).inv ≫
          ((R.mapHomologicalComplex (.up ℕ)).obj K).homologyπ 0 := by
      rw [← cancel_epi (mapExactCyclesIso R K 0).hom]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [f, c]
    rw [← Category.assoc, ← Category.assoc, he']
    simp only [Category.assoc, homologyπ_naturality]
    rfl
  have hf : R.map (I.toRightDerivedZero' G ≫ K.homologyπ 0) ≫ f =
      e.hom.app M ≫ J.toRightDerivedZero' H ≫ L.homologyπ 0 := by
    rw [R.map_comp, Category.assoc, hπ, ← Category.assoc, ← hz, Category.assoc]
  have hN : (G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M) ≫ N.hom =
      I.toRightDerivedZero' G ≫ K.homologyπ 0 := by
    exact normalizationRead _ ((rightDerivedIso G 0).app M)
      (I.isoRightDerivedObj G 0) _ _
      (kummerSourceIndexing_normalization Λ X M 0) (I.toRightDerivedZero_eq G)
  have hP : (H.toRightDerivedZero.app (T.obj M) ≫
      (rightDerivedIso H 0).hom.app (T.obj M)) ≫ P.hom =
      J.toRightDerivedZero' H ≫ L.homologyπ 0 := by
    exact normalizationRead _ ((rightDerivedIso H 0).app (T.obj M))
      (J.isoRightDerivedObj H 0) _ _
      (kummerSourceIndexing_normalization ℤ X (T.obj M) 0) (J.toRightDerivedZero_eq H)
  have hC : (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom ≫ P.hom =
      R.map N.hom ≫ f := by
    exact kummerOriginalMiddle_ordinaryHomology Λ X M 0
  apply (cancel_mono P.hom).1
  change (R.map _ ≫ _) ≫ P.hom = (e.hom.app M ≫ _) ≫ P.hom
  rw [Category.assoc, hC, ← Category.assoc, ← R.map_comp, hN, hf]
  rw [Category.assoc, hP]

end Stacks.EtaleCohomology
end
