/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolution
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The additive presheaf carried by integral convolution

Precomposition in the actual Hom-group factor makes the integral coend an
additive presheaf. The input coefficient presheaves and bifunctor need not
be additive: additivity of the output follows from the Hom-group relation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (F : C ⥤ C ⥤ C)

/-- Precompose the original correspondence component in the coend diagram. -/
def transferDiagram (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X) :
    diagram F P Q X ⟶ diagram F P Q X' :=
  Functor.curry.map (Functor.whiskerRight
    (NatTrans.prod (𝟙 (coefficientModule P Q))
      (Functor.whiskerLeft (Functor.uncurry.obj F)
        (Functor.whiskerRight (preadditiveCoyoneda.map β.op)
          (AddCommGrpCat.uliftFunctor.{max u v w, v} ⋙ integerModuleFunctor))))
    (MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ)))

/-- Transfer of the convolution coend along the original correspondence. -/
def transfer (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X) :
    sections F P Q X ⟶ sections F P Q X' :=
  coend.map (transferDiagram F P Q β)

@[simp]
theorem transfer_generator (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X)
    (Y Z : C) (s : (P.obj (op Y))) (t : (Q.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    transfer F P Q β (generator F P Q X Y Z s t a) =
      generator F P Q X' Y Z s t (β ≫ a) :=
  ConcreteCategory.congr_hom (coend.ι_map (transferDiagram F P Q β) (Y, Z))
    (show ((diagram F P Q X).obj (op (Y, Z))).obj (Y, Z) from
      (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- Addition of source correspondences gives addition of pure generators. -/
theorem generator_add (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X Y Z : C}
    (s : (P.obj (op Y))) (t : (Q.obj (op Z))) (a b : X ⟶ (F.obj Y).obj Z) :
    generator F P Q X Y Z s t (a + b) =
      generator F P Q X Y Z s t a +
        generator F P Q X Y Z s t b := by
  let j := inclusion F P Q X Y Z
  change j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] (ULift.up a + ULift.up b)) =
    j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) + j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up b)
  rw [TensorProduct.tmul_add, map_add]

/-- Addition in the first coefficient acts additively on generators. -/
theorem generator_add_left (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X Y Z : C}
    (s s' : (P.obj (op Y))) (t : (Q.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    generator F P Q X Y Z (s + s') t a =
      generator F P Q X Y Z s t a +
        generator F P Q X Y Z s' t a := by
  simp only [generator]
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add]

/-- Addition in the second coefficient acts additively on generators. -/
theorem generator_add_right (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X Y Z : C}
    (s : (P.obj (op Y))) (t t' : (Q.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    generator F P Q X Y Z s (t + t') a =
      generator F P Q X Y Z s t a +
        generator F P Q X Y Z s t' a := by
  simp only [generator]
  rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]

/-- The integral tensor coend with its original additive transfer action. -/
def presheaf (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w} := by
  let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
  let L : (C)ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
    { obj X := U.obj (sections F P Q X.unop)
      map α := U.map (transfer F P Q α.unop)
      map_id X := by
        rw [← U.map_id]
        apply congrArg U.map
        apply sections_hom_ext
        intro Y Z s t a
        simp only [unop_id, transfer_generator, Category.id_comp,
          ModuleCat.id_apply]
      map_comp α β := by
        rw [← U.map_comp]
        apply congrArg U.map
        apply sections_hom_ext
        intro Y Z s t a
        simp only [unop_comp, ModuleCat.comp_apply, transfer_generator,
          Category.assoc] }
  refine ⟨L, ⟨?_⟩⟩
  intro X Y α β
  change U.map (transfer F P Q (α + β).unop) =
    U.map (transfer F P Q α.unop) + U.map (transfer F P Q β.unop)
  rw [← U.map_add]
  apply congrArg U.map
  apply sections_hom_ext
  intro Z W s t a
  change transfer F P Q (α + β).unop (generator F P Q X.unop Z W s t a) =
    transfer F P Q α.unop (generator F P Q X.unop Z W s t a) +
      transfer F P Q β.unop (generator F P Q X.unop Z W s t a)
  simp only [transfer_generator]
  change generator F P Q Y.unop Z W s t ((α.unop + β.unop) ≫ a) = _
  rw [Preadditive.add_comp, generator_add]


end CategoryTheory.Preadditive.Convolution
