/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCoefficientZero
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIntegralCoefficientRead
public import StacksFrontier.Homology.CompositeCollapseResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero

/-! # The original Ext coefficient comparison in degree zero

The two differently oriented postcomposition comparisons are identified on their actual
resolution formulas. The resulting degree-zero map is exact restriction of Ext followed
by the actual constant-source map.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex ModuleSheafCohomology
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma cancelIsoSandwich {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (j : D ≅ E) (f g : B ⟶ D)
    (h : i.hom ≫ f ≫ j.hom = i.hom ≫ g ≫ j.hom) : f = g := by
  apply (cancel_epi i.hom).1
  apply (cancel_mono j.hom).1
  simpa only [Category.assoc] using h

private lemma cancelRightIso {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ D) (b : A ⟶ B) (i : B ≅ D) (h : b ≫ i.hom = a) :
    a ≫ i.inv = b := by
  rw [← h, Category.assoc, i.hom_inv_id, Category.comp_id]

private lemma cancelLeftIso {C : Type*} [Category C] {A B D : C}
    (i : A ≅ B) (z : B ⟶ D) (v : A ⟶ D) (h : z = i.inv ≫ v) :
    i.hom ≫ z = v := by
  rw [h, ← Category.assoc, i.hom_inv_id, Category.id_comp]

private lemma cancelIsoTail {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (i : D ≅ E) :
    (a ≫ b ≫ i.hom) ≫ i.inv = a ≫ b := by
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma pasteZeroRight {C : Type*} [Category C] {A B D E F G : C}
    (p : A ⟶ B) (g : B ⟶ D) (w : D ⟶ G) (j : D ⟶ E)
    (b : E ⟶ F) (q : F ⟶ G) (t : A ⟶ E) (a : A ⟶ F)
    (hw : w = j ≫ b ≫ q) (ht : p ≫ g ≫ j = t) (ha : t ≫ b = a) :
    p ≫ g ≫ w = a ≫ q := by
  rw [hw]
  simp only [← Category.assoc]
  rw [← Category.assoc] at ht
  rw [ht, ha]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
private theorem originalPostcompose_zero (M : EtaleModules.{u, 0} Λ X) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    (G ⋙ U).toRightDerivedZero.app M ≫
      (Functor.rightDerivedCompIso G U 0).hom.app M = U.map (G.toRightDerivedZero.app M) := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let μ := Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    G U (G ⋙ U) (Iso.refl _) 0
  have hmc : (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso
      G U (G ⋙ U) (Iso.refl _) 0).inv.app I.cocomplex =
      (mapExactHomologyIso U K 0).hom := by
    change homologyMap
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ U)) (.up ℕ)).inv.app
        I.cocomplex) 0 ≫ (mapExactHomologyIso U K 0).hom = _
    have h : ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ U)) (.up ℕ)).inv.app
        I.cocomplex) = 𝟙 _ := rfl
    rw [h, homologyMap_id, Category.id_comp]
  have hμ : μ.inv.app M = (I.isoRightDerivedObj (G ⋙ U) 0).hom ≫
      (mapExactHomologyIso U K 0).hom ≫ U.map (I.isoRightDerivedObj G 0).inv := by
    change (I.isoRightDerivedObj (G ⋙ U) 0).hom ≫
      (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso
        G U (G ⋙ U) (Iso.refl _) 0).inv.app I.cocomplex ≫
      U.map (I.isoRightDerivedObj G 0).inv = _
    rw [hmc]
  have he : (Functor.rightDerivedCompIso G U 0).hom.app M = μ.inv.app M := by
    apply (cancel_epi (I.isoRightDerivedObj (G ⋙ U) 0).inv).1
    rw [Stacks.RightDerivedComp.isoRightDerivedObj_inv_comp_rightDerivedCompIso_hom_app,
      hμ, Iso.inv_hom_id_assoc]
  have hz := Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_zero
    G U (G ⋙ U) (Iso.refl _) M
  change U.map (G.toRightDerivedZero.app M) ≫ μ.hom.app M =
    𝟙 _ ≫ (G ⋙ U).toRightDerivedZero.app M at hz
  rw [Category.id_comp] at hz
  change (G ⋙ U).toRightDerivedZero.app M ≫
    (Functor.rightDerivedCompIso G U 0).hom.app M = U.map (G.toRightDerivedZero.app M)
  rw [he]
  exact cancelRightIso _ _ (μ.app M) hz

set_option backward.isDefEq.respectTransparency false in
private theorem originalExt_zero_read (M : EtaleModules.{u, 0} Λ X) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      Λ X.smallEtaleTopology
    (etaleModuleRightDerivedPlusIsoExt Λ X M 0).inv =
      (extZeroIsoCoyoneda C).hom.app M ≫ α.inv.app M ≫
        U.map (G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M) := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  rw [kummerOriginalComparison_inv_factors]
  simp only [extFunctorObjIsoRightDerived_zero, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.rightDerivedZeroIsoSelf_inv, Category.assoc]
  rw [reassoc_of% (originalPostcompose_zero Λ X M), ← U.map_comp]

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hz (M : EtaleModules.{u, 0} Λ X) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let p := (extZeroIsoCoyoneda C).inv.app M
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M 0).inv
  let S := G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M
  p ≫ z = α.inv.app M ≫ U.map S := by
  intro G U C α p z S
  exact cancelLeftIso ((extZeroIsoCoyoneda C).app M).symm z
    (α.inv.app M ≫ U.map S) (originalExt_zero_read Λ X M)


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hw (M : EtaleModules.{u, 0} Λ X) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let β := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).inv
  let Q := H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M)
  w = (extZeroIsoCoyoneda D).hom.app (T.obj M) ≫ β.inv.app (T.obj M) ≫ V.map Q := by
  intro H T V D β w Q
  exact originalExt_zero_read ℤ X (T.obj M)


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hn (M : EtaleModules.{u, 0} Λ X) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  let S := G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M
  let Q := H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M)
  U.map S ≫ V.map B = V.map (e.hom.app M) ≫ V.map Q := by
  intro G H T U V e B S Q
  have h₀ : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map S ≫ B =
      e.hom.app M ≫ Q := kummerOriginalCoefficient_zero_normalization Λ X M
  have h := congrArg V.map h₀
  rw [V.map_comp, V.map_comp] at h
  exact h


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_ht (M : EtaleModules.{u, 0} Λ X) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let p := (extZeroIsoCoyoneda C).inv.app M
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) 0).app M
  let τ := (kummerConstantRestrictionNatTrans Λ X).app M
  p ≫ g ≫ (extZeroIsoCoyoneda D).hom.app (T.obj M) = τ := by
  intro T C D p g τ
  have h := congrArg (fun η => η.app M)
    (extZeroIsoCoyoneda_inv_comp_extMapComp T (kummerConstantRestrictionNatTrans Λ X))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  exact h


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hτ (M : EtaleModules.{u, 0} Λ X) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let β := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let τ := (kummerConstantRestrictionNatTrans Λ X).app M
  τ ≫ β.inv.app (T.obj M) = α.inv.app M ≫ V.map (e.hom.app M) := by
  intro T V α β e τ
  change (α.inv.app M ≫ V.map (e.hom.app M) ≫ β.hom.app (T.obj M)) ≫
    β.inv.app (T.obj M) = _
  exact cancelIsoTail _ _ (β.app (T.obj M))


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hc (M : EtaleModules.{u, 0} Λ X) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M 0).inv
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).inv
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  A ≫ w = z ≫ V.map B := by
  intro T V z w A B
  exact kummerIntegralCoefficient_cancel_target Λ X M 0


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hleft (M : EtaleModules.{u, 0} Λ X) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let p := (extZeroIsoCoyoneda C).inv.app M
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).inv
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  let Q := H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M)
  p ≫ A ≫ w = α.inv.app M ≫ V.map (e.hom.app M) ≫ V.map Q := by
  intro H T V C α e p w A Q
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M 0).inv
  let B := (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  let S := G.toRightDerivedZero.app M ≫ (rightDerivedIso G 0).hom.app M
  have hz := zero_hz Λ X M
  have hn := zero_hn Λ X M
  have hc := zero_hc Λ X M
  rw [hc, ← Category.assoc, hz, Category.assoc, hn]


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hright (M : EtaleModules.{u, 0} Λ X) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let p := (extZeroIsoCoyoneda C).inv.app M
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).inv
  let Q := H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M)
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) 0).app M
  p ≫ g ≫ w = α.inv.app M ≫ V.map (e.hom.app M) ≫ V.map Q := by
  intro H T V C α e p w Q g
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let β := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  let τ := (kummerConstantRestrictionNatTrans Λ X).app M
  have hw := zero_hw Λ X M
  have ht := zero_ht Λ X M
  have hτ := zero_hτ Λ X M
  have h := pasteZeroRight p g w ((extZeroIsoCoyoneda D).hom.app (T.obj M))
    (β.inv.app (T.obj M)) (V.map Q) τ (α.inv.app M ≫ V.map (e.hom.app M)) hw ht hτ
  exact h.trans (Category.assoc _ _ _)


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
private theorem zero_hA (M : EtaleModules.{u, 0} Λ X) :
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let A := (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom
  let g := (extMapComp T (kummerConstantRestrictionHom Λ X) 0).app M
  A = g := by
  intro T A g
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let p := (extZeroIsoCoyoneda C).inv.app M
  let w := (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).inv
  let Q := H.toRightDerivedZero.app (T.obj M) ≫ (rightDerivedIso H 0).hom.app (T.obj M)
  have hleft := zero_hleft Λ X M
  have hright := zero_hright Λ X M
  exact cancelIsoSandwich ((extZeroIsoCoyoneda C).app M).symm
    (etaleModuleRightDerivedPlusIsoExt ℤ X (T.obj M) 0).symm A g
    (hleft.trans hright.symm)


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- The actual original coefficient comparison is exact restriction of Ext followed
by the actual constant-source map, in degree zero. -/
theorem kummerOriginalCoefficient_zero
    (M : EtaleModules.{u, 0} Λ X)
    (x : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) M 0) :
    (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M 0).hom x =
      (Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
        (x.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X)) (zero_add 0) := by
  exact congrArg (fun y => y x) (zero_hA Λ X M)

end Stacks.EtaleCohomology
end
