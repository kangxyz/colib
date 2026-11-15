/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Center.NegOnePow
/-! # The literal weight-one sign in the native two-variable shift interchange -/
@[expose] public noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  (G : C₁ ⥤ C₂ ⥤ D) [G.CommShift₂Int]

/-- Swapping the native shifts by `-q` and `-1` retains the native shift commutor
and contributes exactly the literal scalar `(-1)^q`. -/
theorem commShift₂_weightOne_interchange (X : C₁) (Y : C₂) (q : ℕ) :
    ((G.obj (X⟦-(q : ℤ)⟧)).commShiftIso (-1 : ℤ)).hom.app Y ≫
      (((G.flip.obj Y).commShiftIso (-(q : ℤ))).hom.app X)⟦(-1 : ℤ)⟧' =
    ((G.flip.obj (Y⟦(-1 : ℤ)⟧)).commShiftIso (-(q : ℤ))).hom.app X ≫
      (((G.obj X).commShiftIso (-1 : ℤ)).hom.app Y)⟦-(q : ℤ)⟧' ≫
      (shiftComm ((G.obj X).obj Y) (-(q : ℤ)) (-1 : ℤ)).inv ≫
        (((-1 : ℤ) ^ q) • 𝟙 _) := by
  simpa only [CommShift₂Setup.int_ε, neg_mul_neg, mul_one,
    CatCenter.app_neg_one_zpow, Units.smul_def, Int.coe_negOnePow_natCast] using
      G.commShift₂_comm CommShift₂Setup.int X Y (-(q : ℤ)) (-1 : ℤ)

end CategoryTheory.Functor
