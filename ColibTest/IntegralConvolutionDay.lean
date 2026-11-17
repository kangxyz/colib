/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.CategoryTheory.Preadditive.IntegralConvolutionDayComparison

/-! The integral Day comparison needs no field, topology, symmetry or additivity of `Q`. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Preadditive.Convolution

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [HasBinaryBiproducts C]
variable (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive]

example : Nonempty (DayConvolution (P ⋙ integerModuleFunctor) (Q ⋙ integerModuleFunctor)) :=
  ⟨dayComparison P Q⟩
