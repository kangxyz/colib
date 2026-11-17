/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.CategoryTheory.Preadditive.IntegralConvolutionMonoidal

/-! # Generic additive convolution client, independent of fields and topologies -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Preadditive.ConvolutionRepresented

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]

example : MonoidalCategory (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  convolutionMonoidalCategory

example : letI := convolutionMonoidalCategory (C := C)
    SymmetricCategory (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  convolutionSymmetricCategory

example : letI := convolutionMonoidalCategory (C := C)
    MonoidalPreadditive (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  convolutionMonoidalPreadditive
