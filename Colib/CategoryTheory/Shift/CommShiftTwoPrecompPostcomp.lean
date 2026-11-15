/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport

/-! # One-variable shifts after precomposition and postcomposition -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CategoryTheory.Functor.CommShift₂

/-- In the first variable, precomposing both variables by `I` and postcomposing
by `V` chooses the composite shift of `I`, the fixed-parameter functor, and `V`. -/
theorem postcompInt_precomp_commShiftFlipObj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (I : C ⥤ D) (V : D ⥤ C) [I.CommShift ℤ] [V.CommShift ℤ] [V.Additive]
    (B : D ⥤ D ⥤ D) [B.CommShift₂Int] (Y : C) :
    let T := (I ⋙ B) ⋙ (Functor.whiskeringLeft C D D).obj I
    Functor.CommShift₂.commShiftFlipObj
        (self := Functor.CommShift₂.postcompInt T V) CommShift₂Setup.int Y =
      Functor.CommShift.comp (I ⋙ B.flip.obj (I.obj Y)) V := by
  intro T
  have hε (m n : ℤ) (Z : D) :
      V.map ((CommShift₂Setup.int.ε m n).val.app Z) =
        (CommShift₂Setup.int.ε m n).val.app (V.obj Z) := by
    simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Units.smul_def,
      V.map_zsmul, V.map_id]
  exact Functor.CommShift₂.postcomp_commShiftFlipObj T V _ _ hε Y

/-- In the second variable, precomposing both variables by `I` and postcomposing
by `V` chooses the composite shift of `I`, the fixed-parameter functor, and `V`. -/
theorem postcompInt_precomp_commShiftObj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (I : C ⥤ D) (V : D ⥤ C) [I.CommShift ℤ] [V.CommShift ℤ] [V.Additive]
    (B : D ⥤ D ⥤ D) [B.CommShift₂Int] (X : C) :
    let T := (I ⋙ B) ⋙ (Functor.whiskeringLeft C D D).obj I
    Functor.CommShift₂.commShiftObj
        (self := Functor.CommShift₂.postcompInt T V) CommShift₂Setup.int X =
      Functor.CommShift.comp (I ⋙ B.obj (I.obj X)) V := by
  intro T
  have hε (m n : ℤ) (Z : D) :
      V.map ((CommShift₂Setup.int.ε m n).val.app Z) =
        (CommShift₂Setup.int.ε m n).val.app (V.obj Z) := by
    simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Units.smul_def,
      V.map_zsmul, V.map_id]
  exact Functor.CommShift₂.postcomp_commShiftObj T V _ _ hε X

end CategoryTheory.Functor.CommShift₂
