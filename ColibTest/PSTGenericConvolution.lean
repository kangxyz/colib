/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionMonoidal

/-! # PST uses the actual generic additive convolution, not a second tensor model -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.PresheafWithTransfers

universe u

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)]
  [MonoidalPreadditive (Cor k)] [SymmetricCategory (Cor k)]

example : convolutionMonoidalCategory (k := k) =
    CategoryTheory.Preadditive.ConvolutionRepresented.convolutionMonoidalCategory.{u + 1, u, 0}
      (C := Cor k) := rfl

example : convolutionMonoidalStruct (k := k) =
    CategoryTheory.Preadditive.ConvolutionRepresented.convolutionMonoidalStruct.{u + 1, u, 0}
      (C := Cor k) := rfl
