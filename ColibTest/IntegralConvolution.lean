/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Convolution

/-! Regression checks for the generic integral coend and its native PST specialization. -/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w

noncomputable section

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (F : C ⥤ C ⥤ C) (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})

-- Neither the coefficients nor the bifunctor carry an additivity assumption.
example (X : C) : HasCoend (diagram F P Q X) := inferInstance

example : (presheaf F P Q).obj.Additive := inferInstance

example (X Y Z : C) (s : P.obj (op Y)) (t : Q.obj (op Z))
    (a : X ⟶ (F.obj Y).obj Z) :
    generator F P Q X Y Z s t a =
      inclusion F P Q X Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) := rfl

end CategoryTheory.Preadditive.Convolution

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k ⥤ Cor k) (P Q : TransferCoefficients k)

-- The old signed-generator API remains definitionally the same inclusion.
example (X Y Z : Cor k) (s : sections P Y) (t : sections Q Z)
    (a : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z s t a =
      convolutionInclusion F P Q X Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) := rfl

end AlgebraicGeometry.PresheafWithTransfers
