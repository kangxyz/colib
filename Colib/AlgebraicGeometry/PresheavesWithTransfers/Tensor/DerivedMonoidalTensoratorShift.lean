/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithfulData
import Colib.CategoryTheory.Shift.CommShiftTwoPrecompPostcomp
import Colib.CategoryTheory.Shift.WhiskeredUnitCommShift

/-! # The signed tensorators of the projective inclusion and equivalence -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "P" => boundedAboveProjectiveCondition k
local notation "J" => BoundedAboveProjectiveHomotopy k
local notation "H" => HomotopyCategory PST (ComplexShape.up ℤ)

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

private instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

attribute [local instance] convolutionHomotopyCommShift₂Int convolutionProjectiveCommShift₂Int

set_option maxHeartbeats 1050000 in
-- Use the actual two-variable shift on the fully faithful inclusion.
/-- The projective inclusion intertwines the original one-variable shifts in both variables. -/
theorem convolutionProjectiveInclusionMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (P).ι ℤ := by
  let I := (P).ι
  let : I.Full := inferInstanceAs ((P).ι.Full)
  let : I.Faithful := inferInstanceAs ((P).ι.Faithful)
  let : I.Additive := inferInstanceAs ((P).ι.Additive)
  let dI : I.CommShift ℤ := inferInstanceAs ((P).ι.CommShift ℤ)
  let := dI
  let T := curriedTensor J ⋙ (Functor.whiskeringRight J J H).obj I
  let : T.CommShift₂Int := convolutionProjectivePostcompCommShift (k := k)
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let G := tensorRight Y
    let H₀ := tensorRight (I.obj Y)
    let dG : G.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := convolutionProjectiveCommShift₂Int (k := k)) CommShift₂Setup.int Y
    let dH : H₀.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := convolutionHomotopyCommShift₂Int (k := k)) CommShift₂Setup.int (I.obj Y)
    let := dH
    let e : G ⋙ I ≅ I ⋙ H₀ := Iso.refl (T.flip.obj Y)
    let t := Functor.LaxMonoidal.μNatTransFst I Y
    have ht : t = e.inv := NatTrans.ext (funext fun X =>
      (Functor.LaxMonoidal.μNatTransFst_app I Y X).trans (ObjectProperty.ι_μ (P) X Y))
    have hd : dG = Functor.CommShift.ofComp e ℤ :=
      Functor.CommShift₂.ofFullyFaithfulInt_commShiftFlipObj I (curriedTensor J) Y
    exact Functor.CommShift.ofComp_compatibility_inv_of_eq I G H₀ dI dG dH e t ht hd
  · let G := tensorLeft X
    let H₀ := tensorLeft (I.obj X)
    let dG : G.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := convolutionProjectiveCommShift₂Int (k := k)) CommShift₂Setup.int X
    let dH : H₀.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := convolutionHomotopyCommShift₂Int (k := k)) CommShift₂Setup.int (I.obj X)
    let := dH
    let e : G ⋙ I ≅ I ⋙ H₀ := Iso.refl (T.obj X)
    let t := Functor.LaxMonoidal.μNatTransSnd I X
    have ht : t = e.inv := NatTrans.ext (funext fun Y =>
      (Functor.LaxMonoidal.μNatTransSnd_app I X Y).trans (ObjectProperty.ι_μ (P) X Y))
    have hd : dG = Functor.CommShift.ofComp e ℤ :=
      Functor.CommShift₂.ofFullyFaithfulInt_commShiftObj I (curriedTensor J) X
    exact Functor.CommShift.ofComp_compatibility_inv_of_eq I G H₀ dI dG dH e t ht hd

variable [HasDerivedCategory.{w} (TransferCoefficients k)]

set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory
  derivedConvolutionInverseMonoidal derivedConvolutionCommShift₂Int

set_option maxHeartbeats 1050000 in
-- The inverse projective equivalence tensorators are the original unit.
/-- Both tensorators of the inverse projective equivalence preserve the chosen shifts. -/
theorem derivedConvolutionInverseMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (E).inverse ℤ := by
  let I := (E).inverse
  let V := (E).functor
  let dI : I.CommShift ℤ := inferInstanceAs ((E).inverse.CommShift ℤ)
  let dV : V.CommShift ℤ := inferInstanceAs ((E).functor.CommShift ℤ)
  let := dI
  let := dV
  let : V.Additive := projectiveEquivalenceFunctorAdditive (k := k)
  let : (E).CommShift ℤ := boundedAboveProjectiveEquivalenceCommShift k
  let η := (E).unitIso.hom
  have hη : NatTrans.CommShift η ℤ :=
    inferInstanceAs (NatTrans.CommShift (E).unitIso.hom ℤ)
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let S := tensorRight (I.obj Y)
    let W := I ⋙ S
    let dS : S.CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := convolutionProjectiveCommShift₂Int (k := k)) CommShift₂Setup.int (I.obj Y)
    let dW : W.CommShift ℤ := Functor.CommShift.compWithData I S dI dS
    let dR : (tensorRight Y).CommShift ℤ := Functor.CommShift₂.commShiftFlipObj
      (self := derivedConvolutionCommShift₂Int (k := k)) CommShift₂Setup.int Y
    let dT : ((W ⋙ V) ⋙ I).CommShift ℤ := Functor.CommShift.compWithData (tensorRight Y) I dR dI
    let dWV := Functor.CommShift.compWithData W V dW dV
    have hRight : dR = dWV :=
      Functor.CommShift₂.postcompInt_precomp_commShiftFlipObj I V (curriedTensor J) Y
    have hd : dT = Functor.CommShift.compWithData (W ⋙ V) I dWV dI :=
      congrArg (fun d => Functor.CommShift.compWithData (tensorRight Y) I d dI) hRight
    let t : W ⟶ (W ⋙ V) ⋙ I := Functor.LaxMonoidal.μNatTransFst I Y
    exact NatTrans.commShift_of_whiskered_unit_app W V I dW dV dI η hη t
      (fun X => derivedConvolutionInverseMonoidal_μ X Y) dT hd
  · let S := tensorLeft (I.obj X)
    let W := I ⋙ S
    let dS : S.CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := convolutionProjectiveCommShift₂Int (k := k)) CommShift₂Setup.int (I.obj X)
    let dW : W.CommShift ℤ := Functor.CommShift.compWithData I S dI dS
    let dL : (tensorLeft X).CommShift ℤ := Functor.CommShift₂.commShiftObj
      (self := derivedConvolutionCommShift₂Int (k := k)) CommShift₂Setup.int X
    let dT : ((W ⋙ V) ⋙ I).CommShift ℤ := Functor.CommShift.compWithData (tensorLeft X) I dL dI
    let dWV := Functor.CommShift.compWithData W V dW dV
    have hLeft : dL = dWV :=
      Functor.CommShift₂.postcompInt_precomp_commShiftObj I V (curriedTensor J) X
    have hd : dT = Functor.CommShift.compWithData (W ⋙ V) I dWV dI :=
      congrArg (fun d => Functor.CommShift.compWithData (tensorLeft X) I d dI) hLeft
    let t : W ⟶ (W ⋙ V) ⋙ I := Functor.LaxMonoidal.μNatTransSnd I X
    exact NatTrans.commShift_of_whiskered_unit_app W V I dW dV dI η hη t
      (fun Y => derivedConvolutionInverseMonoidal_μ X Y) dT hd

end AlgebraicGeometry.PresheafWithTransfers
