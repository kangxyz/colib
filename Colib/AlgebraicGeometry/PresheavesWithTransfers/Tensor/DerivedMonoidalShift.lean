/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalTransport
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
public import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithful
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-! # Signed shift comparisons of the native projective and derived tensors -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)] [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k
local notation "P" => boundedAboveProjectiveCondition k
local notation "J" => BoundedAboveProjectiveHomotopy k
local notation "H" => HomotopyCategory PST (ComplexShape.up ℤ)

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

section Shift

attribute [local instance] convolutionHomotopyCommShift₂Int

private instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

set_option maxHeartbeats 850000 in
-- Transport the two-variable data through the actual full-subcategory inclusion.
open Functor in
/-- The two shift comparisons after inclusion are those of the ambient projective tensor. -/
@[instance_reducible]
def convolutionProjectivePostcompCommShift :
    (curriedTensor J ⋙ (whiskeringRight J J H).obj (P).ι).CommShift₂Int := by
  let T := curriedTensor H
  let I := (P).ι
  change ((I ⋙ T) ⋙ (whiskeringLeft J H H).obj I).CommShift₂Int
  exact Functor.CommShift₂.precomp₂ I (I ⋙ T) CommShift₂Setup.int

/-- The projective full subcategory uses the restriction of the actual signed shift comparison. -/
@[instance_reducible]
def convolutionProjectiveCommShift₂Int : (curriedTensor J).CommShift₂Int := by
  let := convolutionProjectivePostcompCommShift (k := k)
  exact Functor.CommShift₂.ofFullyFaithfulInt (P).ι (curriedTensor J)

attribute [local instance] convolutionProjectiveCommShift₂Int

local instance projectiveEquivalenceFunctorAdditive : ((E).functor).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change DerivedCategory.Qh.map (f.hom + g.hom) =
      DerivedCategory.Qh.map f.hom + DerivedCategory.Qh.map g.hom
    exact Functor.map_add DerivedCategory.Qh

set_option maxHeartbeats 1050000 in
-- Use the chosen projective representative in both variables before localization.
open Functor in
/-- Transport the actual signed projective shift comparison along the native equivalence. -/
@[instance_reducible]
def derivedConvolutionCommShift₂Int : (curriedTensor D).CommShift₂Int := by
  let I := (E).inverse
  let T := curriedTensor J
  let V := (E).functor
  let G := (I ⋙ T) ⋙ (whiskeringLeft D J J).obj I
  change (G ⋙ (whiskeringRight D J D).obj V).CommShift₂Int
  exact Functor.CommShift₂.postcompInt G V

end Shift

end AlgebraicGeometry.PresheafWithTransfers
