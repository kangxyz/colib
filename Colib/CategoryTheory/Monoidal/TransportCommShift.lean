/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Shift.CommShiftTwoMonoidal
public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
import Colib.CategoryTheory.Shift.CommShiftTwoPrecompPostcomp
import Colib.CategoryTheory.Shift.WhiskeredUnitCommShift

/-!
# Shift compatibility of a transported monoidal structure

The inverse monoidal functor preserves the transported two-variable
shift data through the original unit of the equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  (e : C ≌ D) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ] [e.functor.Additive]
  [sourceShift : (curriedTensor C).CommShift₂Int]

/-- Compatibility of the inverse tensorator with the shifts transported along the equivalence. -/
abbrev InverseTensoratorCommShift : Prop :=
  letI := transport e
  letI := Functor.CommShift₂.monoidalTransportInt e
  letI : e.inverse.Monoidal := inferInstanceAs ((equivalenceTransported e).inverse.Monoidal)
  Functor.LaxMonoidal.CommShift e.inverse ℤ

variable [shiftEquivalence : e.CommShift ℤ]

include shiftEquivalence in
/-- The inverse monoidal functor preserves the transported shifts in each
variable through the original equivalence unit. -/
theorem equivalenceTransported_inverse_monoidalCommShift : InverseTensoratorCommShift e := by
  let := transport e
  let := Functor.CommShift₂.monoidalTransportInt e
  let : e.inverse.Monoidal := inferInstanceAs ((equivalenceTransported e).inverse.Monoidal)
  let I : D ⥤ C := e.inverse
  let V : C ⥤ D := e.functor
  let dI : I.CommShift ℤ := inferInstanceAs (e.inverse.CommShift ℤ)
  let dV : V.CommShift ℤ := inferInstanceAs (e.functor.CommShift ℤ)
  let := dI
  let := dV
  let η := e.unitIso.hom
  have hη : NatTrans.CommShift η ℤ :=
    inferInstanceAs (NatTrans.CommShift e.unitIso.hom ℤ)
  have hμ (X Y : D) : Functor.LaxMonoidal.μ I X Y =
      η.app (I.obj X ⊗ I.obj Y) := rfl
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let S : C ⥤ C := tensorRight (I.obj Y)
    let W : D ⥤ C := I ⋙ S
    let dS : S.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := sourceShift) CommShift₂Setup.int (I.obj Y)
    let dW : W.CommShift ℤ := Functor.CommShift.compWithData I S dI dS
    let dR : (tensorRight Y).CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := Functor.CommShift₂.monoidalTransportInt e) CommShift₂Setup.int Y
    let dT : ((W ⋙ V) ⋙ I).CommShift ℤ :=
      Functor.CommShift.compWithData (tensorRight Y) I dR dI
    let dWV := Functor.CommShift.compWithData W V dW dV
    have hRight : dR = dWV :=
      Functor.CommShift₂.postcompInt_precomp_commShiftFlipObj I V (curriedTensor C) Y
    have hd : dT = Functor.CommShift.compWithData (W ⋙ V) I dWV dI :=
      congrArg (fun d => Functor.CommShift.compWithData (tensorRight Y) I d dI) hRight
    let t : W ⟶ (W ⋙ V) ⋙ I := Functor.LaxMonoidal.μNatTransFst I Y
    exact NatTrans.commShift_of_whiskered_unit_app W V I dW dV dI η hη t
      (fun X => hμ X Y) dT hd
  · let S : C ⥤ C := tensorLeft (I.obj X)
    let W : D ⥤ C := I ⋙ S
    let dS : S.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := sourceShift) CommShift₂Setup.int (I.obj X)
    let dW : W.CommShift ℤ := Functor.CommShift.compWithData I S dI dS
    let dL : (tensorLeft X).CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := Functor.CommShift₂.monoidalTransportInt e) CommShift₂Setup.int X
    let dT : ((W ⋙ V) ⋙ I).CommShift ℤ :=
      Functor.CommShift.compWithData (tensorLeft X) I dL dI
    let dWV := Functor.CommShift.compWithData W V dW dV
    have hLeft : dL = dWV :=
      Functor.CommShift₂.postcompInt_precomp_commShiftObj I V (curriedTensor C) X
    have hd : dT = Functor.CommShift.compWithData (W ⋙ V) I dWV dI :=
      congrArg (fun d => Functor.CommShift.compWithData (tensorLeft X) I d dI) hLeft
    let t : W ⟶ (W ⋙ V) ⋙ I := Functor.LaxMonoidal.μNatTransSnd I X
    exact NatTrans.commShift_of_whiskered_unit_app W V I dW dV dI η hη t
      (fun Y => hμ X Y) dT hd

end CategoryTheory.Monoidal
