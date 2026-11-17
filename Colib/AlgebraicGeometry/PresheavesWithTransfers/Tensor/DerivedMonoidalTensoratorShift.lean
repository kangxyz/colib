/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import Colib.CategoryTheory.Monoidal.SubcategoryCommShift
public import Colib.CategoryTheory.Monoidal.TransportCommShift

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
-- Use the generic statement with the original homotopy shift data.
/-- The projective inclusion intertwines the original one-variable shifts in both variables. -/
theorem convolutionProjectiveInclusionMonoidalCommShift :
    ObjectProperty.InclusionTensoratorCommShift
      (C := H) (ambientShift := convolutionHomotopyCommShift₂Int (k := k)) (P) :=
  ObjectProperty.ι_monoidalCommShift
    (C := H) (ambientShift := convolutionHomotopyCommShift₂Int (k := k)) (P)

variable [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] projectiveEquivalenceFunctorAdditive

set_option maxHeartbeats 1050000 in
-- Use the generic statement with the original projective and equivalence shift data.
/-- Both tensorators of the inverse projective equivalence preserve the chosen shifts. -/
theorem derivedConvolutionInverseMonoidalCommShift :
    Monoidal.InverseTensoratorCommShift
      (C := J) (sourceShift := convolutionProjectiveCommShift₂Int (k := k)) (E) :=
  Monoidal.equivalenceTransported_inverse_monoidalCommShift
    (C := J) (sourceShift := convolutionProjectiveCommShift₂Int (k := k)) (E)
    (shiftEquivalence := boundedAboveProjectiveEquivalenceCommShift k)

end AlgebraicGeometry.PresheafWithTransfers
