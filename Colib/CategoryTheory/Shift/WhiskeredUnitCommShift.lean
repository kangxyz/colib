/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.CommShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport

/-! # The shift comparison for a whiskered unit -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

namespace Functor.CommShift

/-- Compose the specified integral shift structures of two functors. -/
@[instance_reducible]
def compWithData {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] (F : C ⥤ D) (G : D ⥤ E)
    (dF : F.CommShift ℤ) (dG : G.CommShift ℤ) : (F ⋙ G).CommShift ℤ :=
  @Functor.CommShift.comp C D E _ _ _ F G ℤ _ _ _ _ dF dG

end Functor.CommShift

namespace NatTrans

open Functor.CommShift (compWithData)

set_option maxHeartbeats 380000 in
-- Compose the generic shift data for the unitor, unit, and associator.
/-- A transformation with the components of a whiskered unit commutes with the shift
after the canonical reassociation and identification of the target shift data. -/
theorem commShift_of_whiskered_unit_app {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (W : C ⥤ D) (V : D ⥤ C) (I : C ⥤ D)
    (dW : W.CommShift ℤ) (dV : V.CommShift ℤ) (dI : I.CommShift ℤ)
    (η : 𝟭 D ⟶ V ⋙ I)
    (hη : @NatTrans.CommShift _ _ _ _ (𝟭 D) (V ⋙ I) η ℤ _ _ _
      (Functor.CommShift.id D) (compWithData V I dV dI))
    (t : W ⟶ (W ⋙ V) ⋙ I) (ht : ∀ X, t.app X = η.app (W.obj X))
    (dT : ((W ⋙ V) ⋙ I).CommShift ℤ)
    (hd : dT = compWithData (W ⋙ V) I (compWithData W V dW dV) dI) :
    @NatTrans.CommShift _ _ _ _ W ((W ⋙ V) ⋙ I) t ℤ _ _ _ dW dT := by
  let := dW
  let := dV
  let := dI
  let := hη
  let a := (Functor.rightUnitor W).symm
  let b := Functor.associator W V I
  let v := Functor.whiskerLeft W η
  let d₁ := compWithData W (𝟭 D) dW (Functor.CommShift.id D)
  let d₂ := compWithData W (V ⋙ I) dW (compWithData V I dV dI)
  let dT₀ := compWithData (W ⋙ V) I (compWithData W V dW dV) dI
  let : NatTrans.CommShift (Functor.rightUnitor W).hom ℤ :=
    NatTrans.CommShift.rightUnitor (F₁ := W) (A := ℤ)
  have ha : NatTrans.CommShift a.hom ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.rightUnitor W) ℤ
  have hb : @NatTrans.CommShift _ _ _ _ ((W ⋙ V) ⋙ I) (W ⋙ (V ⋙ I)) b.hom ℤ _ _ _ dT₀ d₂ :=
    NatTrans.CommShift.associator (F₁ := W) (G := V) (H := I) (A := ℤ)
  have hv : NatTrans.CommShift v ℤ :=
    NatTrans.CommShift.whiskerLeft (F₁ := W) (𝟭 D) (V ⋙ I) η ℤ
  have he : t = a.hom ≫ v ≫ b.inv := by
    apply NatTrans.ext
    funext X
    change t.app X = 𝟙 _ ≫ η.app (W.obj X) ≫ 𝟙 _
    exact (ht X).trans ((Category.id_comp _).trans (Category.comp_id _)).symm
  have h : @NatTrans.CommShift _ _ _ _ W ((W ⋙ V) ⋙ I) t ℤ _ _ _ dW dT₀ :=
    @NatTrans.commShift_of_eq_conj _ _ _ _ ℤ _ _ _ W (W ⋙ 𝟭 D) ((W ⋙ V) ⋙ I) (W ⋙ (V ⋙ I))
      dW d₁ dT₀ d₂ a b ha hb t v hv he
  exact NatTrans.commShift_of_eq_data rfl hd.symm t h

end NatTrans

end CategoryTheory
