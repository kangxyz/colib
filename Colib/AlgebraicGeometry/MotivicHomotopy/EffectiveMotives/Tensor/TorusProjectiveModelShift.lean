/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact
import StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift

/-! # Shift of the original projective torus tensor model -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "NST" => LargeSheaves k
local notation "PST" => LargePresheaves k
local notation "c" => ComplexShape.up ℤ
local notation "S" => nisnevichSheafify k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "Qₚ" => DerivedCategory.Qh (C := PST)
local notation "Qₛ" => DerivedCategory.Qh (C := NST)
local notation "V" => DerivedCategory.Minus.ι (C := NST)

/-- The abelian structure on transfer sheaves for the projective torus model comparison. -/
local instance instAbelianTorusProjectiveModelShift : Abelian NST := SheafWithTransfers.abelian k

private theorem composeSquare {C : Type*} [Category* C] {L : C ⥤ C}
    {A B D : C} {A' B' D' : C}
    {a : A' ⟶ L.obj A} {b : B' ⟶ L.obj B} {d : D' ⟶ L.obj D}
    {f : A ⟶ B} {g : B ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    (hf : a ≫ L.map f = f' ≫ b) (hg : b ≫ L.map g = g' ≫ d) :
    a ≫ L.map (f ≫ g) = (f' ≫ g') ≫ d := by
  rw [L.map_comp, ← Category.assoc a, hf, Category.assoc, hg, Category.assoc]

set_option maxHeartbeats 700000 in
-- Use the component equations of the four concrete comparisons.
/-- On the original projective models, the termwise torus tensor retains the native shift. -/
theorem projectiveTensorModelIso_commShift :
    NatTrans.CommShift (projectiveTensorModelIso k).hom ℤ := by
  let I := projInclusion k
  let P := parameterTensorFunctor Gₘ
  let H := P.mapHomotopyCategory c
  let a := (S).mapDerivedCategoryMinus
  let A := (S).mapDerivedCategory
  let U₀ := DerivedCategory.Minus.ι (C := PST)
  let X := projectiveHomotopyMapToDerivedMinus k P
  let α : X ⋙ U₀ ≅ I ⋙ H ⋙ Qₚ := Iso.refl _
  let β : a ⋙ V ≅ U₀ ⋙ A := Iso.refl _
  let γ := (S).mapDerivedCategoryFactorsh
  let δ := Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ S)) c
  let η := projectiveTensorModelIso k
  let j₁ := Functor.whiskerLeft X β.hom
  let j₂ := Functor.whiskerRight α.hom A
  let j₃ := Functor.whiskerLeft (I ⋙ H) γ.hom
  let j₄ := Functor.whiskerLeft I (Functor.whiskerRight δ.hom Qₛ)
  let : NatTrans.CommShift α.hom ℤ := projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k P
  let : NatTrans.CommShift β.hom ℤ := nisnevichDerivedMinusInclusion_commShift k
  let : NatTrans.CommShift γ.hom ℤ := inferInstance
  let : NatTrans.CommShift δ.hom ℤ := inferInstance
  let : NatTrans.CommShift j₁ ℤ := by dsimp only [j₁]; infer_instance
  let : NatTrans.CommShift j₂ ℤ := NatTrans.CommShift.whiskerRight α.hom A ℤ
  let : NatTrans.CommShift j₃ ℤ := by dsimp only [j₃]; infer_instance
  let : NatTrans.CommShift (Functor.whiskerRight δ.hom Qₛ) ℤ :=
    NatTrans.CommShift.whiskerRight δ.hom Qₛ ℤ
  let : NatTrans.CommShift j₄ ℤ := by dsimp only [j₄]; infer_instance
  have h (K : BoundedAboveProjectiveHomotopy k) :
      η.hom.app K = j₁.app K ≫ j₂.app K ≫ j₃.app K ≫ j₄.app K := by
    simp only [η, j₁, j₂, j₃, j₄, α, β, projectiveTensorModelIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app]
    let x := γ.hom.app ((I ⋙ H).obj K)
    let y := (Qₛ).map (δ.hom.app (I.obj K))
    change x ≫ y = 𝟙 ((a ⋙ V).obj (X.obj K)) ≫ A.map (𝟙 ((X ⋙ U₀).obj K)) ≫ x ≫ y
    exact ((Category.id_comp _).trans
      ((congrArg (· ≫ x ≫ y) (A.map_id ((X ⋙ U₀).obj K))).trans (Category.id_comp _))).symm
  refine ⟨fun n => NatTrans.ext (funext fun K => ?_)⟩
  have h₁ := NatTrans.shift_app_comm j₁ n K
  have h₂ := NatTrans.shift_app_comm j₂ n K
  have h₃ := NatTrans.shift_app_comm j₃ n K
  have h₄ := NatTrans.shift_app_comm j₄ n K
  have h₁₂ : ((X ⋙ (U₀ ⋙ A)).commShiftIso n).hom.app K =
      (((X ⋙ U₀) ⋙ A).commShiftIso n).hom.app K := by
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.comp_obj,
      Functor.map_comp, Category.assoc]
  have h₂₃ : (((I ⋙ H ⋙ Qₚ) ⋙ A).commShiftIso n).hom.app K =
      (((I ⋙ H) ⋙ Qₚ ⋙ A).commShiftIso n).hom.app K := by
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.comp_obj,
      Functor.map_comp, Category.assoc]
  have h₃₄ : (((I ⋙ H) ⋙ (S).mapHomotopyCategory c ⋙ Qₛ).commShiftIso n).hom.app K =
      ((I ⋙ (H ⋙ (S).mapHomotopyCategory c) ⋙ Qₛ).commShiftIso n).hom.app K := by
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.comp_obj,
      Functor.map_comp, Category.assoc]
  change ((X ⋙ a ⋙ V).commShiftIso n).hom.app K ≫ (η.hom.app K)⟦n⟧' =
    η.hom.app (K⟦n⟧) ≫ ((I ⋙ (P ⋙ S).mapHomotopyCategory c ⋙ Qₛ).commShiftIso n).hom.app K
  rw [h, h]
  exact composeSquare (h₁.trans (congrArg (j₁.app (K⟦n⟧) ≫ ·) h₁₂))
    (composeSquare (h₂.trans (congrArg (j₂.app (K⟦n⟧) ≫ ·) h₂₃))
      (composeSquare (h₃.trans (congrArg (j₃.app (K⟦n⟧) ≫ ·) h₃₄)) h₄))

end AlgebraicGeometry.SheafWithTransfers
