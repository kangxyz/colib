/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Colib.CategoryTheory.Preadditive.IntegralConvolution
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

universe u v w

namespace CategoryTheory.Preadditive.ParameterCoend

variable {C : Type u} [Category.{v} C] [Preadditive C]

open CategoryTheory.Preadditive.Convolution (integerModuleFunctor)

/-- The covariant correspondence groups in the second tensor factor. -/
def homModule (F : C ⥤ C) (X : C) :
    C ⥤ ModuleCat.{max u v w} ℤ :=
  F ⋙ preadditiveCoyoneda.obj (op X) ⋙ AddCommGrpCat.uliftFunctor.{max u v w, v} ⋙
    integerModuleFunctor

/-- The two-variable diagram whose coend extends the original parameter product. -/
def diagram (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (X : C) : (C)ᵒᵖ ⥤ C ⥤ ModuleCat.{max u v w} ℤ :=
  Functor.curry.obj
    (((P.obj ⋙ integerModuleFunctor).prod (homModule F X)) ⋙
      MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ))

instance (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X : C) :
    HasCoend (diagram F P X) := by
  let : HasColimitsOfSize.{max u v w, max u v w} AddCommGrpCat.{max u v w} :=
    AddCommGrpCat.hasColimitsOfSize.{max u v w, max u v w, max u v w}
  let : HasColimitsOfSize.{max u v w, max u v w} (ModuleCat.{max u v w} ℤ) := inferInstance
  infer_instance

/-- The native tensor coend of the coefficient and the actual correspondence groups. -/
def sections (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (X : C) : ModuleCat.{max u v w} ℤ :=
  coend (diagram F P X)

/-- A pure tensor from a section and a signed correspondence gives a coend element. -/
def generator (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (X Y : C) (s : (P.obj.obj (op Y))) (a : X ⟶ F.obj Y) :
    sections F P X :=
  (coend.ι (diagram F P X) Y) (s ⊗ₜ[ℤ] ULift.up a)

/-- Dinaturality identifies transferring the section with postcomposition
by the actual image correspondence. -/
theorem generator_transfer (F : C ⥤ C)
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) {X Y Z : C} (f : Y ⟶ Z)
    (s : (P.obj.obj (op Z))) (a : X ⟶ F.obj Y) :
    generator F P X Y (P.obj.map f.op s) a =
      generator F P X Z s (a ≫ F.map f) := by
  let D := diagram F P X
  let A := P.obj ⋙ integerModuleFunctor
  let B := homModule F X
  have h := ConcreteCategory.congr_hom (coend.condition D f)
    (show (D.obj (op Z)).obj Y from s ⊗ₜ[ℤ] ULift.up a)
  change coend.ι D Y ((A.map f.op ⊗ₘ B.map (𝟙 Y)) (s ⊗ₜ[ℤ] ULift.up a)) =
    coend.ι D Z ((A.map (𝟙 (op Z)) ⊗ₘ B.map f) (s ⊗ₜ[ℤ] ULift.up a)) at h
  rw [B.map_id, A.map_id] at h
  exact h

/-- Morphisms from the coend are determined by the literal pure tensors. -/
theorem sections_hom_ext (F : C ⥤ C)
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X : C)
    {M : ModuleCat.{max u v w} ℤ} {f g : sections F P X ⟶ M}
    (h : ∀ (Y : C) (s : (P.obj.obj (op Y))) (a : X ⟶ F.obj Y),
      f (generator F P X Y s a) =
        g (generator F P X Y s a)) : f = g := by
  apply coend.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  change ULift.{max u v w} (X ⟶ F.obj Y) at a
  obtain ⟨a⟩ := a
  exact h Y s a

/-- Precomposition on the correspondence factor gives the transfer of the tensor diagram. -/
def transferDiagram (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    {X X' : C} (β : X' ⟶ X) :
    diagram F P X ⟶ diagram F P X' :=
  Functor.curry.map (Functor.whiskerRight
    (NatTrans.prod (𝟙 (P.obj ⋙ integerModuleFunctor))
      (Functor.whiskerLeft F (Functor.whiskerRight (preadditiveCoyoneda.map β.op)
        (AddCommGrpCat.uliftFunctor.{max u v w, v} ⋙ integerModuleFunctor))))
    (MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ)))

/-- The coend's transfer precomposes the signed correspondence factor. -/
def transfer (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    {X X' : C} (β : X' ⟶ X) :
    sections F P X ⟶ sections F P X' :=
  coend.map (transferDiagram F P β)

@[simp]
theorem transfer_generator (F : C ⥤ C)
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) {X X' : C} (β : X' ⟶ X)
    (Y : C) (s : (P.obj.obj (op Y))) (a : X ⟶ F.obj Y) :
    transfer F P β (generator F P X Y s a) =
      generator F P X' Y s (β ≫ a) :=
  ConcreteCategory.congr_hom (coend.ι_map (transferDiagram F P β) Y)
    (show ((diagram F P X).obj (op Y)).obj Y from s ⊗ₜ[ℤ] ULift.up a)

/-- Addition in the correspondence variable gives the original addition of tensors. -/
theorem generator_add (F : C ⥤ C)
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) {X Y : C} (s : (P.obj.obj (op Y)))
    (a b : X ⟶ F.obj Y) :
    generator F P X Y s (a + b) =
      generator F P X Y s a + generator F P X Y s b := by
  let i : ModuleCat.of ℤ ((P.obj.obj (op Y)) ⊗[ℤ] ULift.{max u v w} (X ⟶ F.obj Y)) ⟶
      sections F P X := coend.ι (diagram F P X) Y
  change i (s ⊗ₜ[ℤ] (ULift.up a + ULift.up b)) =
    i (s ⊗ₜ[ℤ] ULift.up a) + i (s ⊗ₜ[ℤ] ULift.up b)
  rw [TensorProduct.tmul_add, map_add]

/-- Tensoring with the parameter defines an additive transfer presheaf in the source. -/
def presheaf (F : C ⥤ C) (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) := by
  let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
  let L : (C)ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
    { obj X := U.obj (sections F P X.unop)
      map α := U.map (transfer F P α.unop)
      map_id X := by
        rw [← U.map_id]
        apply congrArg U.map
        apply sections_hom_ext
        intro Y s a
        simp only [unop_id, transfer_generator, Category.id_comp,
          ModuleCat.id_apply]
      map_comp α β := by
        rw [← U.map_comp]
        apply congrArg U.map
        apply sections_hom_ext
        intro Y s a
        simp only [unop_comp, ModuleCat.comp_apply, transfer_generator,
          Category.assoc] }
  refine ⟨L, ⟨?_⟩⟩
  intro X Y α β
  change U.map (transfer F P (α + β).unop) =
    U.map (transfer F P α.unop) + U.map (transfer F P β.unop)
  rw [← U.map_add]
  apply congrArg U.map
  apply sections_hom_ext
  intro Z s a
  change transfer F P (α + β).unop (generator F P X.unop Z s a) =
    transfer F P α.unop (generator F P X.unop Z s a) +
    transfer F P β.unop (generator F P X.unop Z s a)
  simp only [transfer_generator]
  change generator F P Y.unop Z s ((α.unop + β.unop) ≫ a) = _
  rw [Preadditive.add_comp, generator_add]

end CategoryTheory.Preadditive.ParameterCoend
