/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalSingleRightComparison
public import Colib.CategoryTheory.Monoidal.TransportedTensorRightCommShift
public import Mathlib.CategoryTheory.Functor.Category
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleShift

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
local notation "E" => boundedAboveProjectiveEquivalence k
local notation "P" => boundedAboveProjectiveCondition k

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

attribute [local instance] derivedConvolutionMonoidalCategory convolutionHomotopyCommShift₂Int
  convolutionProjectiveCommShift₂Int

local instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

attribute [local instance] convolutionBifunctor_flip_additive projectiveEquivalenceFunctorAdditive

section

attribute [local irreducible] convolutionBifunctor

set_option maxHeartbeats 1250000 in
-- Match the factorization theorem with the actual projective quotient and coefficient map.
/-- The first-variable shift on tensoring with a degree-zero projective coefficient
is the original termwise shift. -/
theorem derivedConvolutionSingleRightIso_commShift (A : PST) [Projective A] :
    NatTrans.TransportedTensorRightCommShift
      (sourceShift := convolutionProjectiveCommShift₂Int (k := k)) E
      ((singleDerivedMinus k 0).obj A) (derivedConvolutionSingleRightIso A).hom := by
  let A₀ := (singleDerivedMinus k 0).obj A
  let I := (E).inverse
  let V₀ := (E).functor
  let P₁ := singleProjective A 0
  let j := singleProjectiveComparison A 0
  let V := DerivedCategory.Minus.ι (C := PST)
  let Q := DerivedCategory.Qh (C := PST)
  let J₀ := (P).ι
  let C₀ := (B).flip.obj A
  let F₀ := C₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let L := projectiveHomotopyMapToDerivedMinus k C₀
  let U₂ := tensorRight (J₀.obj P₁)
  let Y := projectiveDerivedMinusFunctor k C₀
  let f : ((I ⋙ tensorRight (I.obj A₀)) ⋙ V₀) ⟶ Y :=
    (derivedConvolutionSingleRightIso A).hom
  let d : V₀ ⋙ V ≅ J₀ ⋙ Q := Iso.refl _
  let e : tensorRight P₁ ⋙ J₀ ≅ J₀ ⋙ U₂ := Iso.refl _
  let c : L ⋙ V ≅ J₀ ⋙ F₀ ⋙ Q := Iso.refl _
  let b : Y ≅ I ⋙ L := Iso.refl _
  let θ : U₂ ⟶ F₀ := (signedTotalHomotopySingleRightIso B A).hom
  have hd : NatTrans.CommShift d.hom ℤ := boundedAboveProjectiveEquivalence_comp_ι_commShift k
  have he : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have hc : NatTrans.CommShift c.hom ℤ :=
    projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k C₀
  have hb : NatTrans.CommShift b.hom ℤ :=
    projectiveDerivedMinusFunctor_comp_projective_commShift k C₀
  have hθ : NatTrans.CommShift θ ℤ := signedTotalHomotopySingleRightIso_commShift B A
  exact NatTrans.transportedTensorRightCommShift_of_factorizationComparison
    (sourceShift := convolutionProjectiveCommShift₂Int (k := k)) E V J₀ Q
    (U₂ := U₂) (F₀ := F₀) (L := L) (Y := Y) A₀ P₁ j.hom d e c b θ hd he hc hb hθ f
    (derivedConvolutionSingleRightIso_hom_throughQuotient A)

end

end AlgebraicGeometry.PresheafWithTransfers
