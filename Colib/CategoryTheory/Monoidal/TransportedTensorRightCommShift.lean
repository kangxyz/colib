/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Functor.FactorizationComparison
public import Colib.CategoryTheory.Shift.CommShiftTwoMonoidal
import Colib.CategoryTheory.Shift.CommShiftTwoPrecompPostcomp
import Colib.CategoryTheory.Shift.WhiskeringComparison
import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport

/-! # Shift compatibility of right tensor comparisons after monoidal transport -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.NatTrans

variable {C J : Type*} [Category* C] [Category* J] [MonoidalCategory J]
  [Preadditive C] [Preadditive J] [HasShift C ℤ] [HasShift J ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor J n).Additive]
  (E : J ≌ C) [E.inverse.CommShift ℤ] [E.functor.CommShift ℤ] [E.functor.Additive]
  [sourceShift : (curriedTensor J).CommShift₂Int]

/-- A comparison out of right tensoring preserves the shift transported along `E`. -/
abbrev TransportedTensorRightCommShift (A : C) {Y : C ⥤ C} [Y.CommShift ℤ]
    (f : ((E.inverse ⋙ tensorRight (E.inverse.obj A)) ⋙ E.functor) ⟶ Y) : Prop :=
  @CommShift _ _ _ _ _ _ f ℤ _ _ _
    (Functor.CommShift₂.commShiftFlipObj
      (self := Functor.CommShift₂.monoidalTransportInt E) CommShift₂Setup.int A)
    inferInstance

/-- A right tensor comparison preserves the transported shift when faithful postcomposition
identifies it with the shift-compatible factorization on the chosen representative. -/
theorem transportedTensorRightCommShift_of_factorizationComparison
    {H D : Type*} [Category* H] [Category* D] [HasShift H ℤ] [HasShift D ℤ]
    (V : C ⥤ D) (J₀ : J ⥤ H) (Q : H ⥤ D)
    [V.CommShift ℤ] [V.Faithful] [J₀.CommShift ℤ] [Q.CommShift ℤ]
    {U₂ F₀ : H ⥤ H} {L : J ⥤ C} {Y : C ⥤ C}
    [U₂.CommShift ℤ] [F₀.CommShift ℤ] [L.CommShift ℤ] [Y.CommShift ℤ]
    (A : C) (P : J) (j : E.inverse.obj A ⟶ P)
    (d : E.functor ⋙ V ≅ J₀ ⋙ Q) (e : tensorRight P ⋙ J₀ ≅ J₀ ⋙ U₂)
    (c : L ⋙ V ≅ J₀ ⋙ F₀ ⋙ Q) (b : Y ≅ E.inverse ⋙ L) (θ : U₂ ⟶ F₀)
    (hd : CommShift d.hom ℤ) (he : CommShift e.hom ℤ) (hc : CommShift c.hom ℤ)
    (hb : CommShift b.hom ℤ) (hθ : CommShift θ ℤ)
    (f : ((E.inverse ⋙ tensorRight (E.inverse.obj A)) ⋙ E.functor) ⟶ Y)
    (hf : let U₀ := tensorRight (E.inverse.obj A)
      let a := Functor.associator E.inverse U₀ E.functor
      let η := (curriedTensor J).flip.map j
      let n := Functor.factorizationComparison d e c η θ
      let a₀ := Functor.isoWhiskerRight a V ≪≫ Functor.associator E.inverse (U₀ ⋙ E.functor) V
      let b₀ := Functor.isoWhiskerRight b V ≪≫ Functor.associator E.inverse L V
      Functor.whiskerRight f V =
        a₀.hom ≫ Functor.whiskerLeft E.inverse n ≫ b₀.inv) :
    TransportedTensorRightCommShift E A f := by
  let U₀ := tensorRight (E.inverse.obj A)
  let a := Functor.associator E.inverse U₀ E.functor
  let η := (curriedTensor J).flip.map j
  let n := Functor.factorizationComparison d e c η θ
  let := hd
  let := he
  let := hc
  let := hb
  let := hθ
  let : CommShift a.hom ℤ := CommShift.associator U₀ E.functor ℤ
  let : CommShift η ℤ := sourceShift.commShift_flip_map j
  let : CommShift n ℤ := Functor.factorizationComparison_commShift d e c η θ
  have h : CommShift f ℤ := commShift_of_whiskerRight_eq_whiskerLeft E.inverse V a b n f hf
  let dT : ((E.inverse ⋙ U₀) ⋙ E.functor).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj
      (self := Functor.CommShift₂.monoidalTransportInt E) CommShift₂Setup.int A
  have hshift : dT = Functor.CommShift.comp (E.inverse ⋙ U₀) E.functor :=
    Functor.CommShift₂.postcompInt_precomp_commShiftFlipObj
      E.inverse E.functor (curriedTensor J) A
  exact commShift_of_eq_data hshift.symm rfl f h

end CategoryTheory.NatTrans
