/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.MonoidalLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.RepresentableLocalization
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidal

/-!
# The effective symmetric monoidal structure

The localization of the signed projective tensor has unit the original
motive of the correspondence unit. Its product of represented motives
is computed by the original finite-correspondence product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
local notation "q" => singularPresheafToEffective k
local notation "M" => effectiveMotive k
local notation "F" => curriedTensor (Cor k)
local notation "s" => BraidedCategory.curriedBraidingNatIso (Cor k)
set_option quotPrecheck false in
local notation "hs" => curriedCorrespondenceBraiding_involutive (k := k)

/-- The abelian structure of the Nisnevich transfer sheaves defining effective convolution. -/
local instance : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

/-- Localization sends the actual derived unit to the original effective motive of the base. -/
def effectiveLocalizationUnitIso : (q).obj (𝟙_ D) ≅ (M).obj (𝟙_ (Cor k)) :=
  (q).mapIso derivedConvolutionUnitIso ≪≫ localizedRepresentableIso (𝟙_ (Cor k))

set_option maxHeartbeats 900000 in
-- Retain the monoidal data of the native localization and its fixed tensor unit.
/-- Effective motives with the canonical localization of signed projective convolution. -/
@[instance_reducible]
def effectiveSignedConvolutionMonoidalCategory
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) : MonoidalCategory E :=
  effectiveConvolutionMonoidalCategory F e s hs
    (derivedConvolutionTensorIso (k := k)) (effectiveLocalizationUnitIso (k := k))

set_option maxHeartbeats 900000 in
-- The same native tensor gives the localized symmetry.
/-- The localized signed tensor is symmetric. -/
@[instance_reducible]
def effectiveSignedConvolutionSymmetricCategory
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    SymmetricCategory E :=
  effectiveConvolutionSymmetricCategory F e s hs derivedConvolutionTensorIso
    effectiveLocalizationUnitIso

/-- Sheafification and effective localization form one strong monoidal functor on
bounded-above transfer presheaf complexes. -/
def effectiveSignedConvolutionLocalizationCoreMonoidal
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (q).CoreMonoidal :=
  effectiveConvolutionLocalizationCoreMonoidal F e s hs derivedConvolutionTensorIso
    effectiveLocalizationUnitIso

/-- The tensor unit is the original motive of the correspondence unit. -/
def effectiveSignedConvolutionUnitIso
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    𝟙_ E ≅ (M).obj (𝟙_ (Cor k)) := Iso.refl _

/-- On the pair of original smooth motives the tensor is the motive of their product. -/
def effectiveSignedConvolutionRepresentableIso
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) (X Y : Cor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (M).obj X ⊗ (M).obj Y ≅ (M).obj (X ⊗ Y) :=
  effectiveConvolutionMonoidalRepresentableIso F e s hs derivedConvolutionTensorIso
    effectiveLocalizationUnitIso X Y

/-- The signed commutation equations with both shifts descend to effective motives. -/
@[instance_reducible]
def effectiveSignedConvolutionCommShift₂Int
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (curriedTensor E).CommShift₂Int :=
  letI := derivedConvolutionCommShift₂Int (k := k)
  effectiveConvolutionMonoidalCommShift₂Int F e s hs derivedConvolutionTensorIso
    effectiveLocalizationUnitIso

set_option maxHeartbeats 1000000 in
-- The integer shift compatibility is attached to the original localization tensorator.
/-- The strong effective localization comparison intertwines the selected tensor shifts. -/
theorem effectiveSignedConvolutionLocalizationMonoidalCommShift
    (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := derivedConvolutionCommShift₂Int (k := k)
    letI := effectiveSignedConvolutionCommShift₂Int e
    letI := (effectiveSignedConvolutionLocalizationCoreMonoidal e).toMonoidal
    Functor.LaxMonoidal.CommShift q ℤ :=
  let := derivedConvolutionCommShift₂Int (k := k)
  effectiveConvolutionLocalizationMonoidalCommShift F e s hs
    (derivedConvolutionTensorIso (k := k)) (effectiveLocalizationUnitIso (k := k))

end AlgebraicGeometry.MotivicHomotopy
