/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCycleMap

/-! # Coefficient compatibility on the actual Ext cocycles

Read the source and target through the monic global-section cycle inclusions.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex Opposite ModuleSheafCohomology
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma pasteCycles {C : Type*} [Category C]
    {A B D E F G H : C} (i : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E)
    (l : E ⟶ F) (k : D ⟶ G) (p : G ⟶ F) (j : B ⟶ H) (q : H ⟶ G)
    (r : A ⟶ H) (h₁ : v ≫ l = k ≫ p) (h₂ : u ≫ k = j ≫ q)
    (h₃ : i ≫ j = r) : (i ≫ u ≫ v) ≫ l = r ≫ q ≫ p := by
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc u k, h₂, Category.assoc, ← Category.assoc i j, h₃]

/-- A square on cycles follows from its image under the monic cycle inclusion. -/
private lemma cyclesSquare {D E : Type*} [Category D] [Category E] [Abelian D]
    (V : D ⥤ E) [V.PreservesMonomorphisms] (L : CochainComplex D ℕ) (q : ℕ)
    {Z Y W : D} {A B C F : E}
    (s : A ⟶ V.obj Z) (c : Z ⟶ L.cycles q) (k : Z ⟶ Y) (e : Y ⟶ W)
    (b : W ⟶ L.X q) (p : A ⟶ C) (α : C ⟶ V.obj Y) (r : A ⟶ B)
    (t : B ⟶ V.obj (L.cycles q)) (f : B ⟶ F) (β : F ⟶ V.obj (L.X q))
    (hc : c ≫ L.iCycles q = k ≫ e ≫ b) (hs : s ≫ V.map k = p ≫ α)
    (ht : t ≫ V.map (L.iCycles q) = f ≫ β)
    (hr : p ≫ α ≫ V.map e ≫ V.map b = r ≫ f ≫ β) : s ≫ V.map c = r ≫ t := by
  apply (cancel_mono (V.map (L.iCycles q))).1
  calc
    (s ≫ V.map c) ≫ V.map (L.iCycles q) = s ≫ V.map (c ≫ L.iCycles q) := by
      rw [Category.assoc, ← V.map_comp]
    _ = s ≫ V.map (k ≫ e ≫ b) := by rw [hc]
    _ = p ≫ α ≫ V.map e ≫ V.map b := by
      rw [V.map_comp, V.map_comp, ← Category.assoc s (V.map k), hs, Category.assoc]
    _ = r ≫ f ≫ β := hr
    _ = (r ≫ t) ≫ V.map (L.iCycles q) := by rw [Category.assoc, ht]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hc (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
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
  c ≫ L.iCycles (n + 1) = R.map (K.iCycles (n + 1)) ≫
      e.hom.app (I.cocomplex.X (n + 1)) ≫ H.map (φ.f (n + 1)) := by
  intro G H R T I J K L e φ a b c
  have he := mapExactCyclesIso_hom_iCycles R K (n + 1)
  have he' : (mapExactCyclesIso R K (n + 1)).inv ≫
      ((R.mapHomologicalComplex (.up ℕ)).obj K).iCycles (n + 1) =
      R.map (K.iCycles (n + 1)) := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact pasteCycles _ _ _ _ _ _ _ _ _ (cyclesMap_i b (n + 1))
    (cyclesMap_i a (n + 1)) he'

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hread (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let β := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let F := extLeftHomologyData J D n
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let r := AddCommGrpCat.ofHom
    (extCocycleComp T I J φ (kummerConstantRestrictionHom Λ X) n)
  E.i ≫ α.inv.app (I.cocomplex.X (n + 1)) ≫
      V.map (e.hom.app (I.cocomplex.X (n + 1))) ≫ V.map (H.map (φ.f (n + 1))) =
      r ≫ F.i ≫ β.inv.app (J.cocomplex.X (n + 1)) := by
  intro H T V I J C D α β E F e φ r
  ext y
  exact (kummerIntegralResolution_corepresentation Λ X M (n + 1) y.val).symm

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient map commutes with the actual cycle corepresentations. -/
theorem kummerOriginalCycles_naturality (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let H := etaleModuleGlobalSections.{u, 0} ℤ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let J := injectiveResolution (T.obj M)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X
  let φ := kummerRestrictedResolutionComparison Λ X M
  let a := (e.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  let b := (H.mapHomologicalComplex (.up ℕ)).map φ
  let c := (mapExactCyclesIso R K (n + 1)).inv ≫ cyclesMap a (n + 1) ≫ cyclesMap b (n + 1)
  let s := originalCocycleToCycles Λ X M n
  let t := originalCocycleToCycles ℤ X (T.obj M) n
  let r := AddCommGrpCat.ofHom
    (extCocycleComp T I J φ (kummerConstantRestrictionHom Λ X) n)
  s ≫ V.map c = r ≫ t := by
  intro G H R T V I J K e φ a b c s t r
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let D := Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let β := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let F := extLeftHomologyData J D n
  let L := (H.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  have hc := succ_hc Λ X M n
  have hs := originalCocycleToCycles_i Λ X M n
  have ht := originalCocycleToCycles_i ℤ X (T.obj M) n
  have hread := succ_hread Λ X M n
  exact cyclesSquare V L (n + 1) s c (R.map (K.iCycles (n + 1)))
    (e.hom.app (I.cocomplex.X (n + 1))) (H.map (φ.f (n + 1)))
    E.i (α.inv.app (I.cocomplex.X (n + 1))) r t F.i
    (β.inv.app (J.cocomplex.X (n + 1))) hc hs ht hread


end Stacks.EtaleCohomology
end
