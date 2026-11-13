/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.UnderlyingTorusUnit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor

/-!
# Maps into the ordinary presheaves of the derived torus kernel

Derived ordinary presheaves carry the original transfer split kernel
to maps annihilated by the original unit restriction. The equivalence
uses the actual reduced inclusion and projection on the two functors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.SheafWithTransfers

open CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "F" => Functor.mapDerivedCategory (toSheaf k) ⋙ ordinaryPresheafDerivedFunctor k
local notation "B" => torusSectionsDerivedFunctor k
local notation "R" => reducedTorusSectionsDerivedFunctor k
local notation "D" => DerivedCategory ((SmoothSite S)ᵒᵖ ⥤ LargeAb k)

omit [HasDerivedCategory (LargePresheaves k)] [HasDerivedCategory (LargeSheaves k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
instance ordinaryPresheafDerivedFunctorCommShift :
    (ordinaryPresheafDerivedFunctor k).CommShift ℤ :=
  Stacks.Injectives.commShiftOfComplexUnit
    (sheafToPresheaf (SmoothSite.nisnevichTopology S) (LargeAb k))
    (ordinaryPresheafDerivedFunctor k) (ordinaryPresheafDerivedUnit k)

omit [HasDerivedCategory (LargePresheaves k)] [HasDerivedCategory (LargeSheaves k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
instance ordinaryPresheafDerivedFunctor_isTriangulated :
    (ordinaryPresheafDerivedFunctor k).IsTriangulated :=
  Stacks.Injectives.isTriangulated_of_complexUnit
    (sheafToPresheaf (SmoothSite.nisnevichTopology S) (LargeAb k))
    (ordinaryPresheafDerivedFunctor k) (ordinaryPresheafDerivedUnit k)

/-- Maps into the original reduced torus summand are exactly the maps into
ordinary derived reindexing whose restriction to parameter one is zero. -/
@[no_expose]
def ordinaryPresheafReducedTorusHomEquiv (X : D) (K : DerivedCategory (LargeSheaves k)) :
    let P := (reindex G (LargeAb k)).mapDerivedCategory
    let ρ := (ordinaryTorusDerivedUnitRestriction k).app ((F).obj K)
    (X ⟶ (F).obj ((R).obj K)) ≃ {f : X ⟶ P.obj ((F).obj K) // f ≫ ρ = 0} := by
  intro P ρ
  let i := (reducedTorusSectionsDerivedInclusion k).app K
  let p := (reducedTorusSectionsDerivedProjection k).app K
  let r := (torusSectionsDerivedUnitRestriction k).app K
  let s := (torusSectionsDerivedConstant k).app K
  let e := (torusSectionsDerivedOrdinaryPresheafIso k).app K
  have hir : i ≫ r = 0 := kernel.condition r
  have hip : i ≫ p = 𝟙 _ := reducedTorusSectionsDerivedInclusion_projection k K
  have hpi : p ≫ i = 𝟙 _ - r ≫ s :=
    reducedTorusSectionsDerivedProjection_inclusion k K
  have he : e.hom ≫ ρ = (F).map r := torusSectionsDerivedOrdinaryPresheafIso_hom_app_unit k K
  have hρ : e.inv ≫ (F).map r = ρ :=
    (congrArg (e.inv ≫ ·) he.symm).trans (e.inv_hom_id_assoc ρ)
  have h₀ : (F).map i ≫ (F).map r = 0 :=
      ((F).map_comp _ _).symm.trans (((F).congr_map hir).trans ((F).map_zero _ _))
  have h₁ : (F).map i ≫ (F).map p = 𝟙 _ :=
    ((F).map_comp _ _).symm.trans (((F).congr_map hip).trans ((F).map_id _))
  have h₂ : (F).map p ≫ (F).map i = 𝟙 _ - (F).map r ≫ (F).map s := by
    rw [← (F).map_comp, hpi, (F).map_sub, (F).map_id, (F).map_comp]
  refine
    { toFun := fun f => ⟨f ≫ (F).map i ≫ e.hom, ?_⟩
      invFun := fun f => f.val ≫ e.inv ≫ (F).map p
      left_inv := ?_
      right_inv := ?_ }
  · simp only [Category.assoc, he, h₀, comp_zero]
  · intro f
    simp only [Category.assoc, e.hom_inv_id_assoc, h₁, Category.comp_id]
  · intro f
    apply Subtype.ext
    change (f.val ≫ e.inv ≫ (F).map p) ≫ (F).map i ≫ e.hom = f.val
    let Y := (F).obj ((B).obj K)
    let a : X ⟶ Y := f.val ≫ e.inv
    let b : Y ⟶ Y := (F).map r ≫ (F).map s
    have hz : a ≫ (F).map r = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (f.val ≫ ·) hρ).trans f.property)
    have hb : a ≫ b = 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (F).map s) hz).trans zero_comp)
    calc
      _ = a ≫ ((F).map p ≫ (F).map i) ≫ e.hom := by
        simp only [a, Category.assoc]
      _ = a ≫ (𝟙 Y - b) ≫ e.hom := congrArg (fun z => a ≫ z ≫ e.hom) h₂
      _ = a ≫ e.hom := by
        rw [← Category.assoc, Preadditive.comp_sub, Category.comp_id, hb, sub_zero]
      _ = f.val := (Category.assoc _ _ _).trans
        ((congrArg (f.val ≫ ·) e.inv_hom_id).trans (Category.comp_id _))

/-- The inverse ordinary reduced comparison acts by its original projection. -/
theorem ordinaryPresheafReducedTorusHomEquiv_symm_apply
    (X : D) (K : DerivedCategory (LargeSheaves k))
    (f : {f : X ⟶ (reindex G (LargeAb k)).mapDerivedCategory.obj ((F).obj K) //
      f ≫ (ordinaryTorusDerivedUnitRestriction k).app ((F).obj K) = 0}) :
    (ordinaryPresheafReducedTorusHomEquiv k X K).symm f =
      f.val ≫ (torusSectionsDerivedOrdinaryPresheafIso k).inv.app K ≫
        (F).map ((reducedTorusSectionsDerivedProjection k).app K) := by
  unfold ordinaryPresheafReducedTorusHomEquiv
  rfl

end AlgebraicGeometry.SheafWithTransfers
