/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Tensor coends for an additive parameter

The coend at `X` uses the integer tensor products of the actual coefficient
groups with the signed groups of correspondences from `X` to the parameter
products. Its dinaturality relation uses the original contravariant transfer
and exterior product on the two factors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Regard the original abelian groups and maps as modules over the integers. -/
def integerModuleFunctor : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id A := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The covariant correspondence groups in the second tensor factor. -/
def parameterCorrespondenceModule (F : Cor k ⥤ Cor k) (X : Cor k) :
    Cor k ⥤ ModuleCat.{u + 1} ℤ :=
  F ⋙ preadditiveCoyoneda.obj (op X) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
    integerModuleFunctor

/-- The two-variable diagram whose coend extends the original parameter product. -/
def parameterTensorDiagram (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k)
    (X : Cor k) : (Cor k)ᵒᵖ ⥤ Cor k ⥤ ModuleCat.{u + 1} ℤ :=
  Functor.curry.obj
    (((P.obj ⋙ integerModuleFunctor).prod (parameterCorrespondenceModule F X)) ⋙
      MonoidalCategory.tensor (ModuleCat.{u + 1} ℤ))

local instance (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    HasCoend (parameterTensorDiagram F P X) := by
  let : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfSize.{u + 1, u + 1, u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} ℤ) := inferInstance
  infer_instance

/-- The native tensor coend of the coefficient and the actual correspondence groups. -/
def parameterTensorSections (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k)
    (X : Cor k) : ModuleCat.{u + 1} ℤ :=
  coend (parameterTensorDiagram F P X)

/-- A pure tensor from a section and a signed correspondence gives a coend element. -/
def parameterTensorGenerator (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k)
    (X Y : Cor k) (s : sections P Y) (a : X ⟶ F.obj Y) :
    parameterTensorSections F P X :=
  (coend.ι (parameterTensorDiagram F P X) Y) (s ⊗ₜ[ℤ] ULift.up a)

/-- Dinaturality identifies transferring the section with postcomposition
by the actual image correspondence. -/
theorem parameterTensorGenerator_transfer (F : Cor k ⥤ Cor k)
    (P : PresheafWithTransfers.{u + 1} k) {X Y Z : Cor k} (f : Y ⟶ Z)
    (s : sections P Z) (a : X ⟶ F.obj Y) :
    parameterTensorGenerator F P X Y (transfer P f s) a =
      parameterTensorGenerator F P X Z s (a ≫ F.map f) := by
  let D := parameterTensorDiagram F P X
  let A := P.obj ⋙ integerModuleFunctor
  let B := parameterCorrespondenceModule F X
  have h := ConcreteCategory.congr_hom (coend.condition D f)
    (show (D.obj (op Z)).obj Y from s ⊗ₜ[ℤ] ULift.up a)
  change coend.ι D Y ((A.map f.op ⊗ₘ B.map (𝟙 Y)) (s ⊗ₜ[ℤ] ULift.up a)) =
    coend.ι D Z ((A.map (𝟙 (op Z)) ⊗ₘ B.map f) (s ⊗ₜ[ℤ] ULift.up a)) at h
  rw [B.map_id, A.map_id] at h
  exact h

/-- Morphisms from the coend are determined by the literal pure tensors. -/
theorem parameterTensorSections_hom_ext (F : Cor k ⥤ Cor k)
    (P : PresheafWithTransfers.{u + 1} k) (X : Cor k)
    {M : ModuleCat.{u + 1} ℤ} {f g : parameterTensorSections F P X ⟶ M}
    (h : ∀ (Y : Cor k) (s : sections P Y) (a : X ⟶ F.obj Y),
      f (parameterTensorGenerator F P X Y s a) =
        g (parameterTensorGenerator F P X Y s a)) : f = g := by
  apply coend.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  change ULift.{u + 1} (X ⟶ F.obj Y) at a
  obtain ⟨a⟩ := a
  exact h Y s a

/-- Precomposition on the correspondence factor gives the transfer of the tensor diagram. -/
def parameterTensorTransferDiagram (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k)
    {X X' : Cor k} (β : X' ⟶ X) :
    parameterTensorDiagram F P X ⟶ parameterTensorDiagram F P X' :=
  Functor.curry.map (Functor.whiskerRight
    (NatTrans.prod (𝟙 (P.obj ⋙ integerModuleFunctor))
      (Functor.whiskerLeft F (Functor.whiskerRight (preadditiveCoyoneda.map β.op)
        (AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙ integerModuleFunctor))))
    (MonoidalCategory.tensor (ModuleCat.{u + 1} ℤ)))

/-- The coend's transfer precomposes the signed correspondence factor. -/
def parameterTensorTransfer (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k)
    {X X' : Cor k} (β : X' ⟶ X) :
    parameterTensorSections F P X ⟶ parameterTensorSections F P X' :=
  coend.map (parameterTensorTransferDiagram F P β)

@[simp]
theorem parameterTensorTransfer_generator (F : Cor k ⥤ Cor k)
    (P : PresheafWithTransfers.{u + 1} k) {X X' : Cor k} (β : X' ⟶ X)
    (Y : Cor k) (s : sections P Y) (a : X ⟶ F.obj Y) :
    parameterTensorTransfer F P β (parameterTensorGenerator F P X Y s a) =
      parameterTensorGenerator F P X' Y s (β ≫ a) :=
  ConcreteCategory.congr_hom (coend.ι_map (parameterTensorTransferDiagram F P β) Y)
    (show ((parameterTensorDiagram F P X).obj (op Y)).obj Y from s ⊗ₜ[ℤ] ULift.up a)

/-- Addition in the correspondence variable gives the original addition of tensors. -/
theorem parameterTensorGenerator_add (F : Cor k ⥤ Cor k)
    (P : PresheafWithTransfers.{u + 1} k) {X Y : Cor k} (s : sections P Y)
    (a b : X ⟶ F.obj Y) :
    parameterTensorGenerator F P X Y s (a + b) =
      parameterTensorGenerator F P X Y s a + parameterTensorGenerator F P X Y s b := by
  let i : ModuleCat.of ℤ (sections P Y ⊗[ℤ] ULift.{u + 1} (X ⟶ F.obj Y)) ⟶
      parameterTensorSections F P X := coend.ι (parameterTensorDiagram F P X) Y
  change i (s ⊗ₜ[ℤ] (ULift.up a + ULift.up b)) =
    i (s ⊗ₜ[ℤ] ULift.up a) + i (s ⊗ₜ[ℤ] ULift.up b)
  rw [TensorProduct.tmul_add, map_add]

/-- Tensoring with the parameter defines an additive transfer presheaf in the source. -/
def parameterTensorPresheaf (F : Cor k ⥤ Cor k) (P : PresheafWithTransfers.{u + 1} k) :
    PresheafWithTransfers.{u + 1} k := by
  let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let L : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj X := U.obj (parameterTensorSections F P X.unop)
      map α := U.map (parameterTensorTransfer F P α.unop)
      map_id X := by
        rw [← U.map_id]
        apply congrArg U.map
        apply parameterTensorSections_hom_ext
        intro Y s a
        simp only [unop_id, parameterTensorTransfer_generator, Category.id_comp,
          ModuleCat.id_apply]
      map_comp α β := by
        rw [← U.map_comp]
        apply congrArg U.map
        apply parameterTensorSections_hom_ext
        intro Y s a
        simp only [unop_comp, ModuleCat.comp_apply, parameterTensorTransfer_generator,
          Category.assoc] }
  refine ⟨L, ⟨?_⟩⟩
  intro X Y α β
  change U.map (parameterTensorTransfer F P (α + β).unop) =
    U.map (parameterTensorTransfer F P α.unop) + U.map (parameterTensorTransfer F P β.unop)
  rw [← U.map_add]
  apply congrArg U.map
  apply parameterTensorSections_hom_ext
  intro Z s a
  change parameterTensorTransfer F P (α + β).unop (parameterTensorGenerator F P X.unop Z s a) =
    parameterTensorTransfer F P α.unop (parameterTensorGenerator F P X.unop Z s a) +
    parameterTensorTransfer F P β.unop (parameterTensorGenerator F P X.unop Z s a)
  simp only [parameterTensorTransfer_generator]
  change parameterTensorGenerator F P Y.unop Z s ((α.unop + β.unop) ≫ a) = _
  rw [Preadditive.add_comp, parameterTensorGenerator_add]

end AlgebraicGeometry.PresheafWithTransfers
