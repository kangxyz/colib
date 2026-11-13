/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor

/-!
# The universal map to parameter sections of the tensor coend

A section at `X` is sent to its pure tensor with the identity correspondence
of the parameter product of `X`. Dinaturality of the coend gives naturality for
the original transfers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local notation "F" => Cor.parameterProduct T

/-- The coefficient map for the parameter adjunction on a pure generator. -/
def parameterTensorUnit (P : PresheafWithTransfers.{u + 1} k) :
    P ⟶ withParameter (parameterTensorPresheaf F P) T :=
  ObjectProperty.homMk
    { app X := by
        let W := (F).obj X.unop
        let j : ModuleCat.of ℤ (sections P X.unop ⊗[ℤ] ULift.{u + 1} (W ⟶ W)) ⟶
            parameterTensorSections F P W := coend.ι (parameterTensorDiagram F P W) X.unop
        let a : ULift.{u + 1} (W ⟶ W) := ULift.up (𝟙 W)
        change sections P X.unop ⟶ AddCommGrpCat.of (parameterTensorSections F P W)
        exact AddCommGrpCat.ofHom
          { toFun := fun s => parameterTensorGenerator F P W X.unop s (𝟙 _)
            map_zero' := by
              change j ((0 : sections P X.unop) ⊗ₜ[ℤ] a) = 0
              rw [TensorProduct.zero_tmul, map_zero]
            map_add' := by
              intro s t
              change j ((s + t) ⊗ₜ[ℤ] a) = j (s ⊗ₜ[ℤ] a) + j (t ⊗ₜ[ℤ] a)
              rw [TensorProduct.add_tmul, map_add] }
      naturality X Y β := by
        apply AddCommGrpCat.ext
        intro s
        change parameterTensorGenerator F P ((F).obj Y.unop) Y.unop (transfer P β.unop s) (𝟙 _) =
          parameterTensorTransfer F P ((F).map β.unop)
            (parameterTensorGenerator F P ((F).obj X.unop) X.unop s (𝟙 _))
        rw [parameterTensorTransfer_generator, Category.comp_id, parameterTensorGenerator_transfer,
          Category.id_comp] }

theorem parameterTensorUnit_app_apply (P : PresheafWithTransfers.{u + 1} k)
    (X : Cor k) (s : sections P X) :
    (parameterTensorUnit T P).hom.app (op X) s =
      parameterTensorGenerator F P ((F).obj X) X s (𝟙 _) := rfl

end AlgebraicGeometry.PresheafWithTransfers
