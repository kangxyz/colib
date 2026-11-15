/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalSingleRightComparison
public import Mathlib.CategoryTheory.Functor.Category
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleShift
import Colib.CategoryTheory.Shift.CommShiftTwoPrecompPostcomp
import Colib.CategoryTheory.Shift.WhiskeringComparison
import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport

/-! # The original shift of tensor with a projective coefficient -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)] [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "B" => convolutionBifunctor F
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k
local notation "P" => boundedAboveProjectiveCondition k
local notation "J" => BoundedAboveProjectiveHomotopy k

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

attribute [local instance] derivedConvolutionMonoidalCategory convolutionHomotopyCommShift₂Int
  convolutionProjectiveCommShift₂Int

local instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

attribute [local instance] convolutionBifunctor_flip_additive

section

attribute [local irreducible] convolutionBifunctor

set_option maxHeartbeats 1250000 in
-- Expose the original quotient comparisons separately before composing them.
/-- The first-variable shift on tensoring with a degree-zero projective coefficient
is the original termwise shift. -/
theorem derivedConvolutionSingleRightIso_commShift (A : PST) [Projective A] :
    letI := derivedConvolutionCommShift₂Int (k := k)
    NatTrans.CommShift (derivedConvolutionSingleRightIso A).hom ℤ := by
  let := derivedConvolutionCommShift₂Int (k := k)
  let I := (E).inverse
  let P₀ := I.obj ((singleDerivedMinus k 0).obj A)
  let P₁ := singleProjective A 0
  let j := singleProjectiveComparison A 0
  let V := DerivedCategory.Minus.ι (C := PST)
  let Q := DerivedCategory.Qh (C := PST)
  let J₀ := (P).ι
  let T := curriedTensor J
  let V₀ := (E).functor
  let C₀ := (B).flip.obj A
  let F₀ := C₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let L := projectiveHomotopyMapToDerivedMinus k C₀
  let U₀ := tensorRight P₀
  let U₁ := tensorRight P₁
  let U₂ := tensorRight (J₀.obj P₁)
  let X := (I ⋙ U₀) ⋙ V₀
  let Y := projectiveDerivedMinusFunctor k C₀
  let f : X ⟶ Y := (derivedConvolutionSingleRightIso A).hom
  let d : V₀ ⋙ V ≅ J₀ ⋙ Q := Iso.refl _
  let d' : L ⋙ V ≅ J₀ ⋙ F₀ ⋙ Q := Iso.refl _
  let : NatTrans.CommShift d.hom ℤ := boundedAboveProjectiveEquivalence_comp_ι_commShift k
  let : NatTrans.CommShift d'.hom ℤ :=
    projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k C₀
  let e₀ := Functor.associator I U₀ V₀
  let : NatTrans.CommShift e₀.hom ℤ := NatTrans.CommShift.associator U₀ V₀ ℤ
  let e₁ : U₁ ⋙ J₀ ≅ J₀ ⋙ U₂ := Iso.refl _
  let : NatTrans.CommShift e₁.hom ℤ := Functor.CommShift.ofComp_compatibility e₁ ℤ
  let e₂ : Y ≅ I ⋙ L := Iso.refl _
  let : NatTrans.CommShift e₂.hom ℤ :=
    projectiveDerivedMinusFunctor_comp_projective_commShift k C₀
  let t := signedTotalHomotopySingleRightIso B A
  let : NatTrans.CommShift t.hom ℤ := signedTotalHomotopySingleRightIso_commShift B A
  let η : U₀ ⟶ U₁ := T.flip.map j.hom
  let : NatTrans.CommShift η ℤ := inferInstanceAs (NatTrans.CommShift (T.flip.map j.hom) ℤ)
  let a := Functor.isoWhiskerRight e₀ V ≪≫ Functor.associator I (U₀ ⋙ V₀) V
  let b := Functor.isoWhiskerRight e₂ V ≪≫ Functor.associator I L V
  let n := Functor.factorizationComparison d e₁ d' η t.hom
  let m := Functor.whiskerLeft I n
  have hu : Functor.whiskerRight f V = a.hom ≫ m ≫ b.inv :=
    derivedConvolutionSingleRightIso_hom_throughQuotient A
  let : NatTrans.CommShift n ℤ := Functor.factorizationComparison_commShift d e₁ d' η t.hom
  have h : NatTrans.CommShift f ℤ :=
    NatTrans.commShift_of_whiskerRight_eq_whiskerLeft I V e₀ e₂ n f hu
  let A₀ := (singleDerivedMinus k 0).obj A
  let : V₀.Additive := projectiveEquivalenceFunctorAdditive (k := k)
  let tensorShift : (tensorRight A₀).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj
      (self := derivedConvolutionCommShift₂Int (k := k)) CommShift₂Setup.int A₀
  have hshift : tensorShift = Functor.CommShift.comp (I ⋙ U₀) V₀ :=
    Functor.CommShift₂.postcompInt_precomp_commShiftFlipObj I V₀ T A₀
  exact NatTrans.commShift_of_eq_data hshift.symm rfl f h

end

end AlgebraicGeometry.PresheafWithTransfers
