/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse

/-!
# Integral convolution diagrams on a preadditive category

The coefficients are ordinary contravariant abelian-group functors. The third
tensor factor is the actual additive Hom group, not the free group on its
underlying set. No additivity of the coefficient functors or of the indexing
bifunctor is required for this coend diagram. No monoidal structure on the
indexing category is assumed.

The coefficient universe contains both the object and Hom universes of the
indexing category; the additional universe parameter permits larger coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.Convolution

/-- Regard abelian groups and their original homomorphisms as integral modules. -/
def integerModuleFunctor : AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id A := by ext x; rfl
  map_comp f g := by ext x; rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The external integral tensor of two coefficient presheaves. -/
def coefficientModule (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    (C × C)ᵒᵖ ⥤ ModuleCat.{max u v w} ℤ :=
  (prodOpEquiv (D := C) C).functor ⋙
    ((P ⋙ integerModuleFunctor).prod (Q ⋙ integerModuleFunctor)) ⋙
      MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ)

variable (F : C ⥤ C ⥤ C)

/-- The additive Hom group into the image of a pair. -/
def homModule (X : C) : C × C ⥤ ModuleCat.{max u v w} ℤ :=
  Functor.uncurry.obj F ⋙ preadditiveCoyoneda.obj (op X) ⋙
    AddCommGrpCat.uliftFunctor.{max u v w, v} ⋙ integerModuleFunctor

/-- The integral diagram with two coefficient factors and the actual Hom group. -/
def diagram (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C) :
    (C × C)ᵒᵖ ⥤ C × C ⥤ ModuleCat.{max u v w} ℤ :=
  Functor.curry.obj
    (((coefficientModule P Q).prod (homModule F X)) ⋙
      MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ))

instance (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C) :
    HasCoend (diagram F P Q X) := by
  let : HasColimitsOfSize.{max u v w, max u v w} AddCommGrpCat.{max u v w} :=
    AddCommGrpCat.hasColimitsOfSize.{max u v w, max u v w, max u v w}
  let : HasColimitsOfSize.{max u v w, max u v w} (ModuleCat.{max u v w} ℤ) := inferInstance
  infer_instance

/-- The integral convolution coend. -/
def sections (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C) :
    ModuleCat.{max u v w} ℤ := coend (diagram F P Q X)

/-- The inclusion of a pair into the coend. -/
def inclusion (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X Y Z : C) :
    ModuleCat.of ℤ (((P.obj (op Y)) ⊗[ℤ] (Q.obj (op Z))) ⊗[ℤ]
      ULift.{max u v w} (X ⟶ (F.obj Y).obj Z)) ⟶ sections F P Q X :=
  coend.ι (diagram F P Q X) (Y, Z)

/-- A pure coefficient pair and an actual additive morphism give a coend generator. -/
def generator (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X Y Z : C)
    (s : P.obj (op Y)) (t : Q.obj (op Z)) (a : X ⟶ (F.obj Y).obj Z) :
    sections F P Q X := inclusion F P Q X Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- The map of the correspondence bifunctor on a pair of arrows. -/
def bifunctorMap {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    (F.obj Y).obj Z ⟶ (F.obj Y').obj Z' :=
  (F.map f).app Z ≫ (F.obj Y').map g

/-- The coend relation is the simultaneous transfer relation in the two factors. -/
theorem generator_transfer (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) {X Y Y' Z Z' : C}
    (f : Y ⟶ Y') (g : Z ⟶ Z') (s : (P.obj (op Y'))) (t : (Q.obj (op Z')))
    (a : X ⟶ (F.obj Y).obj Z) :
    generator F P Q X Y Z (P.map f.op s) (Q.map g.op t) a =
      generator F P Q X Y' Z' s t
        (a ≫ bifunctorMap F f g) := by
  let A := coefficientModule P Q
  let B := homModule F X
  let f' : (Y, Z) ⟶ (Y', Z') := (f, g)
  let j := inclusion F P Q X Y Z
  let j' := inclusion F P Q X Y' Z'
  let C := ModuleCat.of ℤ (((P.obj (op Y')) ⊗[ℤ] (Q.obj (op Z'))) ⊗[ℤ]
      ULift.{max u v w} (X ⟶ (F.obj Y).obj Z))
  let x : C := (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a
  let l : C ⟶ ModuleCat.of ℤ (((P.obj (op Y)) ⊗[ℤ] (Q.obj (op Z))) ⊗[ℤ]
      ULift.{max u v w} (X ⟶ (F.obj Y).obj Z)) := A.map f'.op ⊗ₘ 𝟙 (B.obj (Y, Z))
  let r : C ⟶ ModuleCat.of ℤ (((P.obj (op Y')) ⊗[ℤ] (Q.obj (op Z'))) ⊗[ℤ]
      ULift.{max u v w} (X ⟶ (F.obj Y').obj Z')) := 𝟙 (A.obj (op (Y', Z'))) ⊗ₘ B.map f'
  have h₀ := coend.condition (diagram F P Q X) f'
  change (A.map f'.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫ j =
    (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map f') ≫ j' at h₀
  rw [B.map_id, A.map_id] at h₀
  have h₁ : l ≫ j = r ≫ j' := h₀
  have h₂ : j (l x) = j' (r x) :=
    ConcreteCategory.congr_hom h₁ x
  change j (((P.map f.op s) ⊗ₜ[ℤ] (Q.map g.op t)) ⊗ₜ[ℤ] ULift.up a) =
    j' ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up (a ≫ bifunctorMap F f g)) at h₂
  exact h₂

/-- Maps from the coend are determined by its actual pure generators. -/
theorem sections_hom_ext (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C)
    {M : ModuleCat.{max u v w} ℤ} {f g : sections F P Q X ⟶ M}
    (h : ∀ (Y Z : C) (s : (P.obj (op Y))) (t : (Q.obj (op Z)))
      (a : X ⟶ (F.obj Y).obj Z),
      f (generator F P Q X Y Z s t a) =
        g (generator F P Q X Y Z s t a)) : f = g := by
  apply coend.hom_ext
  rintro ⟨Y, Z⟩
  let j := inclusion F P Q X Y Z
  change j ≫ f = j ≫ g
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro st ⟨a⟩
  refine TensorProduct.inductionOn st (fun s t => h Y Z s t a) ?_
  intro s t hs ht
  let W := ModuleCat.of ℤ (((P.obj (op Y)) ⊗[ℤ] (Q.obj (op Z))) ⊗[ℤ]
    ULift.{max u v w} (X ⟶ (F.obj Y).obj Z))
  let a₁ : W := s ⊗ₜ[ℤ] ULift.up a
  let a₂ : W := t ⊗ₜ[ℤ] ULift.up a
  have hsum : (s + t) ⊗ₜ[ℤ] ULift.up a = (a₁ + a₂ : W) := TensorProduct.add_tmul _ _ _
  calc
    (j ≫ f).hom ((s + t) ⊗ₜ[ℤ] ULift.up a) = (j ≫ f).hom (a₁ + a₂) := congrArg _ hsum
    _ = (j ≫ f).hom a₁ + (j ≫ f).hom a₂ := (j ≫ f).hom.map_add a₁ a₂
    _ = (j ≫ g).hom a₁ + (j ≫ g).hom a₂ := congrArg₂ (· + ·) hs ht
    _ = (j ≫ g).hom (a₁ + a₂) := ((j ≫ g).hom.map_add a₁ a₂).symm
    _ = (j ≫ g).hom ((s + t) ⊗ₜ[ℤ] ULift.up a) := congrArg _ hsum.symm

end CategoryTheory.Preadditive.Convolution
