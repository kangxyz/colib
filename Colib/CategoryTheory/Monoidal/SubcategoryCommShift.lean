/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Shift.CommShiftTwoMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithfulData

/-! # Shift compatibility of a full monoidal subcategory inclusion -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [ambientShift : (curriedTensor C).CommShift₂Int]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsStableUnderShift ℤ]

/-- Compatibility of the inclusion tensorator with the restricted integral shifts. -/
abbrev InclusionTensoratorCommShift : Prop :=
  letI := Functor.CommShift₂.restrictMonoidalInt P
  Functor.LaxMonoidal.CommShift P.ι ℤ

set_option maxHeartbeats 1050000 in
-- Identify the one-variable shifts reflected along the actual inclusion.
/-- The tensorator of the full-subcategory inclusion preserves the restricted shifts. -/
theorem ι_monoidalCommShift : InclusionTensoratorCommShift P := by
  let := Functor.CommShift₂.restrictMonoidalInt P
  let I : P.FullSubcategory ⥤ C := P.ι
  let : I.Full := inferInstanceAs (P.ι.Full)
  let : I.Faithful := inferInstanceAs (P.ι.Faithful)
  let : I.Additive := inferInstanceAs (P.ι.Additive)
  let dI : I.CommShift ℤ := inferInstanceAs (P.ι.CommShift ℤ)
  let := dI
  let T : P.FullSubcategory ⥤ P.FullSubcategory ⥤ C :=
    curriedTensor P.FullSubcategory ⋙
      (Functor.whiskeringRight P.FullSubcategory P.FullSubcategory C).obj I
  let : T.CommShift₂Int := Functor.CommShift₂.restrictMonoidalPostcompInt P
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let G := tensorRight Y
    let H := tensorRight (I.obj Y)
    let dG : G.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := Functor.CommShift₂.restrictMonoidalInt P) CommShift₂Setup.int Y
    let dH : H.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := ambientShift) CommShift₂Setup.int (I.obj Y)
    let := dH
    let e : G ⋙ I ≅ I ⋙ H := Iso.refl (T.flip.obj Y)
    let t : I ⋙ H ⟶ G ⋙ I := Functor.LaxMonoidal.μNatTransFst I Y
    have ht : t = e.inv := NatTrans.ext (funext fun X =>
      (Functor.LaxMonoidal.μNatTransFst_app I Y X).trans (ι_μ P X Y))
    have hd : dG = Functor.CommShift.ofComp e ℤ :=
      Functor.CommShift₂.ofFullyFaithfulInt_commShiftFlipObj I (curriedTensor P.FullSubcategory) Y
    exact Functor.CommShift.ofComp_compatibility_inv_of_eq I G H dI dG dH e t ht hd
  · let G := tensorLeft X
    let H := tensorLeft (I.obj X)
    let dG : G.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := Functor.CommShift₂.restrictMonoidalInt P) CommShift₂Setup.int X
    let dH : H.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := ambientShift) CommShift₂Setup.int (I.obj X)
    let := dH
    let e : G ⋙ I ≅ I ⋙ H := Iso.refl (T.obj X)
    let t : I ⋙ H ⟶ G ⋙ I := Functor.LaxMonoidal.μNatTransSnd I X
    have ht : t = e.inv := NatTrans.ext (funext fun Y =>
      (Functor.LaxMonoidal.μNatTransSnd_app I X Y).trans (ι_μ P X Y))
    have hd : dG = Functor.CommShift.ofComp e ℤ :=
      Functor.CommShift₂.ofFullyFaithfulInt_commShiftObj I (curriedTensor P.FullSubcategory) X
    exact Functor.CommShift.ofComp_compatibility_inv_of_eq I G H dI dG dH e t ht hd

end CategoryTheory.ObjectProperty
