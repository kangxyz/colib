/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithful

/-! # The one-variable data of fully faithful shift reflection -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

namespace Functor.CommShift

/-- An inverse comparison commutes with the shift when its source shift is the
one reflected by `ofComp`. -/
theorem ofComp_compatibility_inv_of_eq {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (I : C ⥤ D) [I.Full] [I.Faithful]
    (L : C ⥤ C) (R : D ⥤ D) (dI : I.CommShift ℤ)
    (dL : L.CommShift ℤ) (dR : R.CommShift ℤ) (e : L ⋙ I ≅ I ⋙ R)
    (t : I ⋙ R ⟶ L ⋙ I) (ht : t = e.inv)
    (hd : dL = (letI := dI; letI := dR; Functor.CommShift.ofComp e ℤ)) :
    letI := dI
    letI := dL
    letI := dR
    NatTrans.CommShift t ℤ := by
  subst dL
  subst t
  let := dI
  let := dR
  let := Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact NatTrans.CommShift.of_iso_inv e ℤ

end Functor.CommShift

namespace Functor.CommShift₂

/-- The first-variable shift of `ofFullyFaithfulInt` is reflected through the
identity comparison after postcomposition. -/
theorem ofFullyFaithfulInt_commShiftFlipObj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (I : C ⥤ D) [I.Full] [I.Faithful] [I.Additive] [I.CommShift ℤ] (B : C ⥤ C ⥤ C)
    [(B ⋙ (Functor.whiskeringRight C C D).obj I).CommShift₂Int] (Y : C) :
    let T := B ⋙ (Functor.whiskeringRight C C D).obj I
    let e : B.flip.obj Y ⋙ I ≅ T.flip.obj Y := Iso.refl (T.flip.obj Y)
    Functor.CommShift₂.commShiftFlipObj
        (self := Functor.CommShift₂.ofFullyFaithfulInt I B) CommShift₂Setup.int Y =
      Functor.CommShift.ofComp e ℤ := (rfl)

/-- The second-variable shift of `ofFullyFaithfulInt` is reflected through the
identity comparison after postcomposition. -/
theorem ofFullyFaithfulInt_commShiftObj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (I : C ⥤ D) [I.Full] [I.Faithful] [I.Additive] [I.CommShift ℤ] (B : C ⥤ C ⥤ C)
    [(B ⋙ (Functor.whiskeringRight C C D).obj I).CommShift₂Int] (X : C) :
    let T := B ⋙ (Functor.whiskeringRight C C D).obj I
    let e : B.obj X ⋙ I ≅ T.obj X := Iso.refl (T.obj X)
    Functor.CommShift₂.commShiftObj
        (self := Functor.CommShift₂.ofFullyFaithfulInt I B) CommShift₂Setup.int X =
      Functor.CommShift.ofComp e ℤ := (rfl)

end Functor.CommShift₂

end CategoryTheory
