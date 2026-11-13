/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.UnderlyingTorusDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedBaseSummand
public import Colib.CategoryTheory.Sites.Simplicial.ParameterCoproductPoint
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products
import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare

/-!
# The torus unit on ordinary derived presheaves

Restriction to the unit is pullback along the original unit section
of the smooth product. The derived comparison retains that restriction
under graph restriction and passage to the original derived presheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers
open CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct
open Stacks.DerivedFunctor

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "V" => toPresheaf k
local notation "T" => withParameterFunctor G
local notation "A" => LargeAb k
local notation "P" => reindex G A
local notation "c" => ComplexShape.up ℤ

/-- The original family of unit sections of the torus over smooth objects. -/
def torusUnitPoint : 𝟭 (SmoothSite S) ⟶ (Functor.const (SmoothSite S)).obj G where
  app X := SmoothSite.Contraction.toBase X ≫ SmoothSite.torusOne S
  naturality _ _ f := by
    change f ≫ (SmoothSite.Contraction.toBase _ ≫ SmoothSite.torusOne S) =
      (SmoothSite.Contraction.toBase _ ≫ SmoothSite.torusOne S) ≫ 𝟙 G
    rw [← Category.assoc, SmoothSite.Contraction.comp_toBase, Category.comp_id]

private theorem pointGraph_torusUnitPoint (X : SmoothSite S) :
    (pointGraph G (torusUnitPoint k)).app X ≫ (SmoothSite.categoricalProductIso X G).hom =
      SmoothSite.Contraction.unitSection.app X := by
  apply SmoothSite.product_hom_ext
  · rw [Category.assoc, SmoothSite.categoricalProductIso_hom_fst]
    exact (prod.lift_fst _ _).trans (SmoothSite.productLift_fst _ _).symm
  · rw [Category.assoc, SmoothSite.categoricalProductIso_hom_snd]
    exact (prod.lift_snd _ _).trans (SmoothSite.productLift_snd _ _).symm

private theorem graphRestriction_torusPresheafUnit_app_app
    (M : LargePresheaves k) (X : SmoothSite S) :
    ((V).map ((torusPresheafUnitNatTrans k).app M)).app (op X) =
      ((V).obj M).map (SmoothSite.Contraction.unitSection.app X).op := by
  let U := Cor.graphFunctor k
  let e := SmoothSite.Contraction.productBaseIso X
  let f := SmoothSite.productMap (𝟙 X) (SmoothSite.torusOne S)
  change transfer M (U.map f) ≫ transfer M (U.map e.inv) =
    transfer M (U.map (SmoothSite.Contraction.unitSection.app X))
  rw [← transfer_comp, ← U.map_comp, SmoothSite.Contraction.baseProduct_unit]

private theorem comp_pullback_at_point
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (D₀ : Cᵒᵖ ⥤ D) {U Y W : C} (a : U ⟶ Y) (b : Y ⟶ W) (f : U ⟶ W)
    (h : a ≫ b = f) :
    D₀.map b.op ≫ D₀.map a.op = D₀.map f.op :=
  (D₀.map_comp _ _).symm.trans (D₀.congr_map (congrArg (fun g => g.op) h))

set_option maxHeartbeats 600000 in
-- The graph and categorical product restrictions retain independent chosen limits.
private theorem torusGraphRestrictionIso_hom_app_unit_at
    (M : LargePresheaves k) (X : (SmoothSite S)ᵒᵖ) :
    let z := (torusGraphRestrictionIso k).hom.app M
    let u := (pointRestriction G A (torusUnitPoint k)).app ((V).obj M)
    let v := (V).map ((torusPresheafUnitNatTrans k).app M)
    z.app X ≫ u.app X = v.app X := by
  intro z u v
  let F := (V).obj M
  let a := (pointGraph G (torusUnitPoint k)).app X.unop
  let b := (SmoothSite.categoricalProductIso X.unop G).hom
  have hz : z.app X = F.map b.op := torusGraphRestrictionIso_hom_app_app k M X.unop
  have hu : u.app X = F.map a.op := by
    unfold u pointRestriction
    rfl
  have hv : v.app X = F.map (SmoothSite.Contraction.unitSection.app X.unop).op :=
    graphRestriction_torusPresheafUnit_app_app k M X.unop
  have hb : a ≫ b = SmoothSite.Contraction.unitSection.app X.unop :=
    pointGraph_torusUnitPoint k X.unop
  calc
    _ = F.map b.op ≫ F.map a.op := congrArg₂ (· ≫ ·) hz hu
    _ = _ := (comp_pullback_at_point F a b _ hb).trans hv.symm

/-- The ordinary graph comparison sends the original transfer restriction
to restriction along the actual parameter point. -/
theorem torusGraphRestrictionIso_hom_app_unit (M : LargePresheaves k) :
    (torusGraphRestrictionIso k).hom.app M ≫
      (pointRestriction G A (torusUnitPoint k)).app ((V).obj M) =
    (V).map ((torusPresheafUnitNatTrans k).app M) := by
  apply NatTrans.ext
  funext X
  exact torusGraphRestrictionIso_hom_app_unit_at k M X

section DerivedPresheaf

variable [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]

/-- Restriction to the actual unit on the exact ordinary reindexing of derived presheaves. -/
def ordinaryTorusDerivedUnitRestriction : (P).mapDerivedCategory ⟶ 𝟭 _ :=
  mapDerivedNatTrans (pointRestriction G A (torusUnitPoint k)) ≫
    (Functor.mapDerivedCategoryIdIso _).hom

omit [HasDerivedCategory (LargePresheaves k)] in
/-- Derived ordinary restriction is induced by the actual cochain point restriction. -/
theorem ordinaryTorusDerivedUnitRestriction_app_Q_obj
    (K : CochainComplex ((SmoothSite S)ᵒᵖ ⥤ A) ℤ) :
    (P).mapDerivedCategoryFactors.inv.app K ≫
      (ordinaryTorusDerivedUnitRestriction k).app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((homologicalPointRestriction G A (torusUnitPoint k) c).app K) := by
  let a := pointRestriction G A (torusUnitPoint k)
  let t := mapDerivedNatTrans a
  let C := (SmoothSite S)ᵒᵖ ⥤ A
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let e := (P).mapDerivedCategoryFactors.app K
  let i := (𝟭 C).mapDerivedCategoryFactors.app K
  let j := (Functor.mapHomologicalComplexIdIso C c).hom.app K
  have ht : t.app (Q.obj K) ≫ i.hom = e.hom ≫ Q.map ((a.mapHomologicalComplex c).app K) :=
    mapDerivedNatTrans_factors_app a K
  have hj : (Functor.mapDerivedCategoryIdIso C).hom.app (Q.obj K) = i.hom ≫ Q.map j :=
    Functor.mapDerivedCategoryIdIso_hom_app K
  change e.inv ≫ (t.app (Q.obj K) ≫ (Functor.mapDerivedCategoryIdIso C).hom.app (Q.obj K)) = _
  calc
    _ = e.inv ≫ (t.app (Q.obj K) ≫ i.hom) ≫ Q.map j := by
      rw [hj]
      exact congrArg (e.inv ≫ ·) (Category.assoc _ _ _).symm
    _ = e.inv ≫ (e.hom ≫ Q.map ((a.mapHomologicalComplex c).app K)) ≫ Q.map j :=
      congrArg (fun m => e.inv ≫ m ≫ Q.map j) ht
    _ = _ := by
      simp only [Category.assoc, e.inv_hom_id_assoc]
      exact (Q.map_comp _ _).symm

private theorem derivedTorusGraphRestrictionIso_hom_app_unit
    (K : DerivedCategory (LargePresheaves k)) :
    (Functor.mapDerivedCategorySquareIso (torusGraphRestrictionIso k)).hom.app K ≫
      (ordinaryTorusDerivedUnitRestriction k).app ((V).mapDerivedCategory.obj K) =
    (V).mapDerivedCategory.map ((torusPresheafDerivedUnitRestriction k).app K) := by
  let C := LargePresheaves k
  let D := (SmoothSite S)ᵒᵖ ⥤ A
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let Q' : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let v := (V).mapDerivedCategory
  let p := (P).mapDerivedCategory
  let t := (T : C ⥤ C)
  let ρ := torusPresheafDerivedUnitRestriction k
  let σ := ordinaryTorusDerivedUnitRestriction k
  let e := Functor.mapDerivedCategorySquareIso (torusGraphRestrictionIso k)
  have h (L : CochainComplex C ℤ) : e.hom.app (Q.obj L) ≫ σ.app (v.obj (Q.obj L)) =
      v.map (ρ.app (Q.obj L)) := by
    let W := (V).mapHomologicalComplex c
    let a := (t.mapDerivedCategoryFactors.app L)
    let b := ((V).mapDerivedCategoryFactors.app L)
    let b' := ((V).mapDerivedCategoryFactors.app ((t.mapHomologicalComplex c).obj L))
    let d := ((P).mapDerivedCategoryFactors.app (W.obj L))
    let f := (Functor.mapHomologicalComplexCompIso (torusGraphRestrictionIso k) c).hom.app L
    let l := (presheafComplexRestriction k).app L
    let m := (homologicalPointRestriction G A (torusUnitPoint k) c).app (W.obj L)
    have hco : f ≫ m = W.map l := by
      apply HomologicalComplex.hom_ext
      intro i
      let M := L.X i
      let U : LargePresheaves k ⥤ D := V
      let f₁ := (torusGraphRestrictionIso k).hom.app M
      let f₂ := (pointRestriction G A (torusUnitPoint k)).app (U.obj M)
      change f₁ ≫ (f₂ ≫ 𝟙 _) = U.map ((torusPresheafUnitNatTrans k).app M ≫ 𝟙 _)
      rw [Category.comp_id, Category.comp_id]
      exact torusGraphRestrictionIso_hom_app_unit k M
    have hρ : a.inv ≫ ρ.app (Q.obj L) = Q.map l :=
      torusPresheafDerivedUnitRestriction_app_Q_obj k L
    have hσ : d.inv ≫ σ.app (Q'.obj (W.obj L)) = Q'.map m :=
      ordinaryTorusDerivedUnitRestriction_app_Q_obj k (W.obj L)
    have he : e.hom.app (Q.obj L) =
        v.map a.hom ≫ b'.hom ≫ Q'.map f ≫ d.inv ≫ p.map b.inv :=
      Functor.mapDerivedCategorySquareIso_hom_app_Q (torusGraphRestrictionIso k) L
    have hν : p.map b.inv ≫ σ.app (v.obj (Q.obj L)) =
        σ.app (Q'.obj (W.obj L)) ≫ b.inv := σ.naturality b.inv
    have hν' : p.map b.inv ≫ σ.app (v.obj (Q.obj L)) ≫ b.hom =
        σ.app (Q'.obj (W.obj L)) := by
      calc
        _ = (p.map b.inv ≫ σ.app (v.obj (Q.obj L))) ≫ b.hom :=
          (Category.assoc _ _ _).symm
        _ = (σ.app (Q'.obj (W.obj L)) ≫ b.inv) ≫ b.hom := congrArg (· ≫ b.hom) hν
        _ = _ := (Category.assoc _ _ _).trans
          ((congrArg (σ.app (Q'.obj (W.obj L)) ≫ ·) b.inv_hom_id).trans (Category.comp_id _))
    apply (cancel_mono b.hom).1
    calc
      _ = v.map a.hom ≫ b'.hom ≫ Q'.map f ≫ Q'.map m := by
        rw [he]
        simp only [Category.assoc, hν', hσ]
      _ = v.map a.hom ≫ b'.hom ≫ Q'.map (W.map l) := by
        exact congrArg (fun z => v.map a.hom ≫ b'.hom ≫ z)
          ((Q'.map_comp f m).symm.trans (Q'.congr_map hco))
      _ = v.map (a.hom ≫ Q.map l) ≫ b.hom := by
        have hn : v.map (Q.map l) ≫ b.hom = b'.hom ≫ Q'.map (W.map l) :=
          (V).mapDerivedCategoryFactors.hom.naturality l
        exact (congrArg (v.map a.hom ≫ ·) hn.symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ b.hom) (v.map_comp _ _).symm))
      _ = _ := by
        rw [← hρ, a.hom_inv_id_assoc]
  let α := e.hom ≫ Functor.whiskerLeft v σ
  let β := Functor.whiskerRight ρ v
  have hab : α = β := Localization.natTrans_ext Q
    (HomologicalComplex.quasiIso C c) h
  exact NatTrans.congr_app hab K

end DerivedPresheaf

section DerivedSheaf

variable [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- On derived ordinary presheaves the original torus unit is still
restriction along the same smooth unit section. -/
theorem torusSectionsDerivedOrdinaryPresheafIso_hom_app_unit
    (K : DerivedCategory (LargeSheaves k)) :
    let F := (toSheaf k).mapDerivedCategory ⋙ ordinaryPresheafDerivedFunctor k
    (torusSectionsDerivedOrdinaryPresheafIso k).hom.app K ≫
      (ordinaryTorusDerivedUnitRestriction k).app (F.obj K) =
    F.map ((torusSectionsDerivedUnitRestriction k).app K) := by
  intro F
  let U := forgetDerivedFunctor k
  let B := torusSectionsDerivedFunctor k
  let e := forgetDerivedOrdinaryPresheafIso k
  let v := (V).mapDerivedCategory
  let p := (P).mapDerivedCategory
  let d := Functor.mapDerivedCategorySquareIso (torusGraphRestrictionIso k)
  let a := (torusSectionsDerivedForgetIso k).hom.app K
  let r := (torusSectionsDerivedUnitRestriction k).app K
  let ρ := (torusPresheafDerivedUnitRestriction k).app (U.obj K)
  let σ := ordinaryTorusDerivedUnitRestriction k
  have he : (torusSectionsDerivedOrdinaryPresheafIso k).hom.app K =
      e.inv.app (B.obj K) ≫ v.map a ≫ d.hom.app (U.obj K) ≫ p.map (e.hom.app K) :=
    torusSectionsDerivedOrdinaryPresheafIso_hom_app k K
  have hρ : a ≫ ρ = U.map r := torusSectionsDerivedForgetIso_hom_app_unitRestriction k K
  have hd : d.hom.app (U.obj K) ≫ σ.app (v.obj (U.obj K)) = v.map ρ :=
    derivedTorusGraphRestrictionIso_hom_app_unit k (U.obj K)
  have hσ : p.map (e.hom.app K) ≫ σ.app (F.obj K) =
      σ.app (v.obj (U.obj K)) ≫ e.hom.app K := σ.naturality (e.hom.app K)
  have hn : v.map (U.map r) ≫ e.hom.app K = e.hom.app (B.obj K) ≫ F.map r :=
    e.hom.naturality r
  change (torusSectionsDerivedOrdinaryPresheafIso k).hom.app K ≫ σ.app (F.obj K) =
    F.map r
  calc
    _ = e.inv.app (B.obj K) ≫ v.map a ≫ d.hom.app (U.obj K) ≫
        σ.app (v.obj (U.obj K)) ≫ e.hom.app K := by
      rw [he]
      simp only [Category.assoc]
      exact congrArg (fun z => e.inv.app (B.obj K) ≫ v.map a ≫ d.hom.app (U.obj K) ≫ z) hσ
    _ = e.inv.app (B.obj K) ≫ v.map (U.map r) ≫ e.hom.app K := by
      rw [reassoc_of% hd, ← v.map_comp_assoc, hρ]
    _ = _ := by
      exact (congrArg (e.inv.app (B.obj K) ≫ ·) hn).trans
        (e.inv_hom_id_app_assoc (B.obj K) (F.map r))

end DerivedSheaf

end AlgebraicGeometry.SheafWithTransfers
