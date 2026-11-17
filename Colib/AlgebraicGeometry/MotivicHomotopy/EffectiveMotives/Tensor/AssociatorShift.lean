/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.AssociatorShiftDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.CoherentConvolution
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.CochainAssociatorShift
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.HomotopyMonoidalQuotient
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalTensoratorShift

/-! # Middle shift compatibility of the effective tensor associator -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
local notation "q" => singularPresheafToEffective k
local notation "W" => effectivePresheafEquivalences k
local notation "F" => curriedTensor (Cor k)

local notation "Ch" => CochainComplex PST ℤ
local notation "H" => HomotopyCategory PST (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient PST (ComplexShape.up ℤ)

private instance : (boundedAboveProjectiveCondition k).IsStableUnderShift ℤ :=
  (inferInstance : (boundedAboveProjectiveCondition k).IsTriangulated).toIsStableUnderShift

attribute [local instance] convolutionMonoidalCategory convolutionMonoidalPreadditive
  convolutionCurriedTensor_additive convolutionTensorLeft_additive
  convolutionCochainMonoidalCategory convolutionCochainCommShift₂Int
  convolutionHomotopyMonoidalCategory convolutionHomotopyCommShift₂Int
  boundedAboveProjectiveCondition_convolution_isMonoidal convolutionProjectiveCommShift₂Int

local instance convolutionAssociatorHasTensor (X Y : GradedObject ℤ PST) :
    GradedObject.HasTensor X Y :=
  cochainTensorHasCoproducts X Y

local instance convolutionAssociatorHasGoodTensor₁₂ (X Y Z : GradedObject ℤ PST) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  cochainTensorPreservesCoproducts₁₂ X Y Z

local instance convolutionAssociatorHasGoodTensor₂₃ (X Y Z : GradedObject ℤ PST) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  cochainTensorPreservesCoproducts₂₃ X Y Z

local instance convolutionAssociatorHasTensor₄ (X Y Z V : GradedObject ℤ PST) :
    GradedObject.HasTensor₄ObjExt X Y Z V :=
  cochainTensorPreservesCoproducts₄ X Y Z V

local instance convolutionAssociatorTensorLeftPreservesInitial (X : PST) :
    CategoryTheory.Limits.PreservesColimit (Functor.empty.{0} PST) (tensorLeft X) :=
  convolutionTensorLeft_preservesInitial X

local instance convolutionAssociatorTensorRightPreservesInitial (X : PST) :
    CategoryTheory.Limits.PreservesColimit (Functor.empty.{0} PST) (tensorRight X) :=
  convolutionTensorRight_preservesInitial X

/-- The actual middle associator on cochains is compatible with the original signed shifts. -/
theorem convolutionCochain_middleAssociatorCommShift :
    MiddleAssociatorCommShift Ch := by
  apply (middleAssociatorCommShift_iff Ch).2
  intro A X L n
  rw [convolutionCochain_commShiftIso_hom, convolutionCochain_commShiftIso_hom,
    convolutionCochain_commShiftIso_flip_hom, convolutionCochain_commShiftIso_flip_hom]
  exact CochainComplex.associator_hom_middleShift A X L n

/-- The actual middle-associator shift comparison descends through homotopy. -/
theorem convolutionHomotopy_middleAssociatorCommShift :
    MiddleAssociatorCommShift H := by
  let := convolutionHomotopyQuotientMonoidal (k := k)
  let := convolutionHomotopyQuotientMonoidalCommShift (k := k)
  let : (Q).EssSurj := ⟨fun X => ⟨X.as, ⟨Iso.refl _⟩⟩⟩
  let := TensorCommShift.of_commShift₂ H CommShift₂Setup.int
  exact middleAssociatorCommShift_of_strongMonoidal Q convolutionCochain_middleAssociatorCommShift

/-- Shift compatibility reflects to the actual projective full subcategory. -/
theorem convolutionProjective_middleAssociatorCommShift :
    MiddleAssociatorCommShift (BoundedAboveProjectiveHomotopy k) := by
  let I := (boundedAboveProjectiveCondition k).ι
  let := convolutionProjectiveInclusionMonoidalCommShift (k := k)
  exact middleAssociatorCommShift_of_faithful I convolutionHomotopy_middleAssociatorCommShift

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

section Transport

attribute [local instance] projectiveEquivalenceFunctorAdditive

/-- The actual derived associator preserves the signed shift in the middle variable. -/
theorem derivedConvolution_middleAssociatorCommShift :
    Monoidal.TransportedMiddleAssociatorCommShift
      (C := BoundedAboveProjectiveHomotopy k)
      (sourceShift := convolutionProjectiveCommShift₂Int (k := k))
      (boundedAboveProjectiveEquivalence k) :=
  Monoidal.middleAssociatorCommShift_transport
    (C := BoundedAboveProjectiveHomotopy k)
    (sourceShift := convolutionProjectiveCommShift₂Int (k := k))
    (boundedAboveProjectiveEquivalence k)
    (shiftEquivalence := boundedAboveProjectiveEquivalenceCommShift k)
    convolutionProjective_middleAssociatorCommShift

end Transport

variable [PerfectField k] [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The abelian structure of the transfer sheaves used in the effective associator comparison. -/
local instance associatorShiftAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

/-- The middle-associator shift equation descends along the actual effective localization. -/
theorem effectiveSignedConvolution_middleAssociatorCommShift
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    MiddleAssociatorCommShift E :=
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let := (effectiveSignedConvolutionLocalizationCoreMonoidal e).toMonoidal
  let := effectiveSignedConvolutionLocalizationMonoidalCommShift e
  let := Localization.essSurj q W
  let := TensorCommShift.of_commShift₂ E CommShift₂Setup.int
  middleAssociatorCommShift_of_strongMonoidal q derivedConvolution_middleAssociatorCommShift

end AlgebraicGeometry.MotivicHomotopy
