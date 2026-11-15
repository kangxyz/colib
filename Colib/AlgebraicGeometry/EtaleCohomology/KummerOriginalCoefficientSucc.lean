/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCycleComparison

/-! # The original coefficient Ext map in positive degrees

Paste the actual cycle square, original normalizers, and original derived coefficient map.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex Opposite ModuleSheafCohomology
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma inverseSquare {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : D ⟶ E) (i : D ≅ A) (j : E ≅ B)
    (h : b ≫ j.hom = i.hom ≫ a) : a ≫ j.inv = i.inv ≫ b := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma mapCancel {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E : C} (i : B ≅ E) (x : A ⟶ E) :
    F.map x ≫ F.map i.inv ≫ F.map i.hom = F.map x := by
  rw [← F.map_comp, i.inv_hom_id, F.map_id, Category.comp_id]

private lemma cancelTwoTails {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (f g : B ⟶ D) (i : D ≅ E) (j : E ≅ F)
    (h : p ≫ f ≫ i.hom ≫ j.hom = p ≫ g ≫ i.hom ≫ j.hom) : p ≫ f = p ≫ g := by
  apply (cancel_mono i.hom).1
  apply (cancel_mono j.hom).1
  simpa only [Category.assoc] using h

private lemma mappedInverseSquare {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (V : D ⥤ E) {A B : C} {F G : D} (i : A ≅ B) (j : F ≅ G)
    (f : R.obj A ⟶ F) (g : R.obj B ⟶ G)
    (h : f ≫ j.hom = R.map i.hom ≫ g) :
    V.map (R.map i.inv) ≫ V.map f ≫ V.map j.hom = V.map g := by
  rw [← V.map_comp, h, ← V.map_comp, ← Category.assoc, ← R.map_comp,
    i.inv_hom_id, R.map_id, Category.id_comp]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hπ (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let c := (mapExactCyclesIso R K (n + 1)).inv ≫ cyclesMap a (n + 1) ≫ cyclesMap b (n + 1)
  let f := (mapExactHomologyIso R K (n + 1)).inv ≫
    homologyMap a (n + 1) ≫ homologyMap b (n + 1)
  R.map (K.homologyπ (n + 1)) ≫ f = c ≫ L.homologyπ (n + 1) := by
  intro G H R T I J K L e φ a b c f
  have he := homologyπ_mapExactHomologyIso_hom R K (n + 1)
  have he' : R.map (K.homologyπ (n + 1)) ≫ (mapExactHomologyIso R K (n + 1)).inv =
      (mapExactCyclesIso R K (n + 1)).inv ≫
        ((R.mapHomologicalComplex (.up ℕ)).obj K).homologyπ (n + 1) := by
    exact inverseSquare _ _ _ _ he
  dsimp only [f, c]
  rw [← Category.assoc, ← Category.assoc, he']
  simp only [Category.assoc, homologyπ_naturality]
  rfl

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hhom (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let f := (mapExactHomologyIso R K (n + 1)).inv ≫
    homologyMap a (n + 1) ≫ homologyMap b (n + 1)
  let s := originalCocycleToCycles Λ X M n
  let t := originalCocycleToCycles ℤ X (T.obj M) n
  let r := AddCommGrpCat.ofHom
    (extCocycleComp T I J φ (kummerConstantRestrictionHom Λ X) n)
  s ≫ U.map (K.homologyπ (n + 1)) ≫ V.map f =
      r ≫ t ≫ V.map (L.homologyπ (n + 1)) := by
  intro G H R T U V I J K L e φ a b f s t r
  have hcycles := kummerOriginalCycles_naturality Λ X M n
  have hπ := succ_hπ Λ X M n
  change s ≫ V.map (R.map (K.homologyπ (n + 1))) ≫ V.map f = _
  rw [← V.map_comp, hπ, V.map_comp, ← Category.assoc, hcycles, Category.assoc]

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hcancel (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1 : ℕ)).hom
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M (n + 1)).inv
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) (n + 1)).inv
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1)).hom
  A ≫ w = z ≫ V.map B := by
  intro T V B z w A
  exact kummerIntegralCoefficient_cancel_target Λ X M (n + 1)

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hmid (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let N := derivedPlusResolutionHomologyIso G I (n + 1) ≪≫
    extendedHomologyIso G I.cocomplex (n + 1)
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  let f := (mapExactHomologyIso R K (n + 1)).inv ≫
    homologyMap a (n + 1) ≫ homologyMap b (n + 1)
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1 : ℕ)).hom
  B ≫ P.hom = R.map N.hom ≫ f := by
  intro G H R T I J K e φ a b N P f B
  dsimp only [P, N, f, a, b, B, Iso.trans_hom]
  exact kummerOriginalMiddle_ordinaryHomology Λ X M (n + 1)

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hmidInv (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let N := derivedPlusResolutionHomologyIso G I (n + 1) ≪≫
    extendedHomologyIso G I.cocomplex (n + 1)
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  let f := (mapExactHomologyIso R K (n + 1)).inv ≫
    homologyMap a (n + 1) ≫ homologyMap b (n + 1)
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1 : ℕ)).hom
  U.map N.inv ≫ V.map B ≫ V.map P.hom = V.map f := by
  intro G H R T U V I J K e φ a b N P f B
  have hmid := succ_hmid Λ X M n
  exact mappedInverseSquare R V N P B f hmid

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hleft (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  let f := (mapExactHomologyIso R K (n + 1)).inv ≫
    homologyMap a (n + 1) ≫ homologyMap b (n + 1)
  let s := originalCocycleToCycles Λ X M n
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) (n + 1)).inv
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1)).hom
  E.π ≫ A ≫ w ≫ V.map P.hom =
      s ≫ U.map (K.homologyπ (n + 1)) ≫ V.map f := by
  intro G H R T U V I J C E K e φ a b P f s w A
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M (n + 1)).inv
  have hsource := kummerOriginalExtCocycle_read Λ X M n
  have hmidInv := succ_hmidInv Λ X M n
  have hcancel := succ_hcancel Λ X M n
  rw [← Category.assoc A, hcancel]
  simp only [Category.assoc]
  rw [← Category.assoc E.π z, hsource]
  simp only [Category.assoc]
  rw [hmidInv]

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hext (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let F := extLeftHomologyData J D n
  let φ := kummerRestrictedResolutionComparison Λ X M
  let r := AddCommGrpCat.ofHom
    (extCocycleComp T I J φ (kummerConstantRestrictionHom Λ X) n)
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) (n + 1)).app M
  E.π ≫ g = r ≫ F.π := by
  intro T I J C D E F φ r g
  exact extMapComp_π T I J φ (kummerRestrictedResolutionComparison_augmentation Λ X M)
    (kummerConstantRestrictionHom Λ X) n

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_htarget (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let J := injectiveResolution (T.obj M)
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let F := extLeftHomologyData J D n
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  let t := originalCocycleToCycles ℤ X (T.obj M) n
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) (n + 1)).inv
  F.π ≫ w = t ≫ V.map (L.homologyπ (n + 1)) ≫ V.map P.inv := by
  intro H T V J D F L P t w
  exact kummerOriginalExtCocycle_read ℤ X (T.obj M) n

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hright (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let φ := kummerRestrictedResolutionComparison Λ X M
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  let t := originalCocycleToCycles ℤ X (T.obj M) n
  let r := AddCommGrpCat.ofHom
    (extCocycleComp T I J φ (kummerConstantRestrictionHom Λ X) n)
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) (n + 1)).app M
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) (n + 1)).inv
  E.π ≫ g ≫ w ≫ V.map P.hom =
      r ≫ t ≫ V.map (L.homologyπ (n + 1)) := by
  intro H T V I J C E L φ P t r g w
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let F := extLeftHomologyData J D n
  have htarget := succ_htarget Λ X M n
  have hext := succ_hext Λ X M n
  rw [← Category.assoc E.π g, hext]
  simp only [Category.assoc]
  rw [← Category.assoc F.π w, htarget]
  simp only [Category.assoc]
  exact congrArg (fun y => r ≫ t ≫ y) (mapCancel V P (L.homologyπ (n + 1)))

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hA (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) (n + 1)).app M
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1)).hom
  A = g := by
  intro T g A
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let P := derivedPlusResolutionHomologyIso H J (n + 1) ≪≫
    extendedHomologyIso H J.cocomplex (n + 1)
  have hhom := succ_hhom Λ X M n
  have hleft := succ_hleft Λ X M n
  have hright := succ_hright Λ X M n
  have hpost := cancelTwoTails E.π A g
    (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) (n + 1)).symm (V.mapIso P)
    (hleft.trans (hhom.trans hright.symm))
  exact Cofork.IsColimit.hom_ext E.hπ hpost

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- The actual original coefficient comparison is exact restriction of Ext followed
by the actual constant-source map, in positive degree. -/
theorem kummerOriginalCoefficient_succ
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (x : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
      M (n + 1)) :
    (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1)).hom x =
      (Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
        (x.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X))
        (zero_add (n + 1)) := by
  exact congrArg (fun y => y x) (succ_hA Λ X M n)


end Stacks.EtaleCohomology
end
