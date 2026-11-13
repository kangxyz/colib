/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor

/-!
# Evaluation from the parameter tensor coend

A map to parameter sections induces evaluation of a pure tensor by the
actual transfer of its signed correspondence. Transfer naturality is
exactly the dinaturality relation for this evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
variable {P Q : PresheafWithTransfers.{u + 1} k}

local notation "F" => Cor.parameterProduct T

/-- Evaluate the actual signed transfer against the value of a coefficient map. -/
def parameterTensorPairing (θ : P ⟶ withParameter Q T) (X Y : Cor k) :
    ((parameterTensorDiagram F P X).obj (op Y)).obj Y ⟶
      ModuleCat.of ℤ (sections Q X) := by
  let h : sections P Y ⟶ sections Q ((F).obj Y) := θ.hom.app (op Y)
  let ev (s : sections P Y) : ULift.{u + 1} (X ⟶ (F).obj Y) →+ sections Q X :=
    { toFun := fun a => transfer Q a.down (h s)
      map_zero' := by rw [show (0 : ULift.{u + 1} (X ⟶ (F).obj Y)).down = 0 from rfl,
        transfer_zero]; rfl
      map_add' a b := by
        change transfer Q (a.down + b.down) _ = _
        rw [transfer_add]
        rfl }
  let e : sections P Y →+ (ULift.{u + 1} (X ⟶ (F).obj Y) →ₗ[ℤ] sections Q X) :=
    { toFun := fun s => (ev s).toIntLinearMap
      map_zero' := by
        ext a
        change transfer Q a.down (h 0) = 0
        rw [map_zero, map_zero]
      map_add' s t := by
        ext a
        change transfer Q a.down (h (s + t)) =
          transfer Q a.down (h s) + transfer Q a.down (h t)
        rw [map_add, map_add] }
  exact ModuleCat.ofHom (TensorProduct.lift e.toIntLinearMap)

@[simp]
theorem parameterTensorPairing_tmul (θ : P ⟶ withParameter Q T) (X Y : Cor k)
    (s : sections P Y) (a : ULift.{u + 1} (X ⟶ (F).obj Y)) :
    parameterTensorPairing T θ X Y (s ⊗ₜ[ℤ] a) = transfer Q a.down (θ.hom.app (op Y) s) := rfl

/-- The transfer pairing identifies the two maps in the coend relation. -/
theorem parameterTensorPairing_dinatural (θ : P ⟶ withParameter Q T)
    (X : Cor k) {Y Z : Cor k} (f : Y ⟶ Z) :
    ((parameterTensorDiagram F P X).map f.op).app Y ≫ parameterTensorPairing T θ X Y =
      ((parameterTensorDiagram F P X).obj (op Z)).map f ≫ parameterTensorPairing T θ X Z := by
  let A := P.obj ⋙ integerModuleFunctor
  let B := parameterCorrespondenceModule F X
  change (A.map f.op ⊗ₘ B.map (𝟙 Y)) ≫ parameterTensorPairing T θ X Y =
    (A.map (𝟙 (op Z)) ⊗ₘ B.map f) ≫ parameterTensorPairing T θ X Z
  rw [A.map_id, B.map_id]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  change ULift.{u + 1} (X ⟶ (F).obj Y) at a
  have h := ConcreteCategory.congr_hom (transfer_naturality θ f) s
  change θ.hom.app (op Y) (transfer P f s) =
    transfer Q ((F).map f) (θ.hom.app (op Z) s) at h
  change transfer Q a.down (θ.hom.app (op Y) (transfer P f s)) =
    transfer Q (a.down ≫ (F).map f) (θ.hom.app (op Z) s)
  rw [h, transfer_comp]
  rfl

/-- The native coend map induced by the transfer pairing. -/
def parameterTensorDescApp (θ : P ⟶ withParameter Q T) (X : Cor k) :
    parameterTensorSections F P X ⟶ ModuleCat.of ℤ (sections Q X) :=
  coend.desc («F» := parameterTensorDiagram F P X) (parameterTensorPairing T θ X)
    (fun _ _ f => parameterTensorPairing_dinatural T θ X f)

/-- On every generator the coend map is the actual signed transfer. -/
@[simp]
theorem parameterTensorDescApp_generator (θ : P ⟶ withParameter Q T) (X Y : Cor k)
    (s : sections P Y) (a : X ⟶ (F).obj Y) :
    parameterTensorDescApp T θ X (parameterTensorGenerator F P X Y s a) =
      transfer Q a (θ.hom.app (op Y) s) := by
  change (coend.ι (parameterTensorDiagram F P X) Y ≫
    parameterTensorDescApp T θ X) (s ⊗ₜ[ℤ] ULift.up a) = _
  rw [parameterTensorDescApp, coend.ι_desc]
  exact parameterTensorPairing_tmul T θ X Y s (ULift.up a)

/-- Evaluation from the coend commutes with every actual source correspondence. -/
@[reassoc]
theorem parameterTensorDescApp_naturality (θ : P ⟶ withParameter Q T)
    {X X' : Cor k} (β : X' ⟶ X) :
    parameterTensorTransfer F P β ≫ parameterTensorDescApp T θ X' =
      parameterTensorDescApp T θ X ≫ integerModuleFunctor.map (transfer Q β) := by
  apply parameterTensorSections_hom_ext
  intro Y s a
  change parameterTensorDescApp T θ X' (parameterTensorTransfer F P β
    (parameterTensorGenerator F P X Y s a)) =
      transfer Q β (parameterTensorDescApp T θ X (parameterTensorGenerator F P X Y s a))
  rw [parameterTensorTransfer_generator, parameterTensorDescApp_generator,
    parameterTensorDescApp_generator, transfer_comp]
  rfl

/-- Descend the original coefficient pairing as a morphism with transfers. -/
def parameterTensorDesc (θ : P ⟶ withParameter Q T) : parameterTensorPresheaf F P ⟶ Q :=
  ObjectProperty.homMk
    { app X := (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (parameterTensorDescApp T θ X.unop)
      naturality X Y β := by
        let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
        change U.map (parameterTensorTransfer F P β.unop) ≫
          U.map (parameterTensorDescApp T θ Y.unop) =
          U.map (parameterTensorDescApp T θ X.unop) ≫
            U.map (integerModuleFunctor.map (transfer Q β.unop))
        exact (U.map_comp _ _).symm.trans
          ((congrArg (fun f => U.map f) (parameterTensorDescApp_naturality T θ β.unop)).trans
            (U.map_comp _ _)) }

@[simp]
theorem parameterTensorDesc_app_generator (θ : P ⟶ withParameter Q T) (X Y : Cor k)
    (s : sections P Y) (a : X ⟶ (F).obj Y) :
    (parameterTensorDesc T θ).hom.app (op X) (parameterTensorGenerator F P X Y s a) =
      transfer Q a (θ.hom.app (op Y) s) :=
  parameterTensorDescApp_generator T θ X Y s a

end AlgebraicGeometry.PresheafWithTransfers
