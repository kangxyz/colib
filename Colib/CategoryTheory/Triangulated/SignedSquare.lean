/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Square.ShortComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Basic

/-! # Triangles of signed squares with a given connecting morphism -/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Square

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

section

variable [HasShift C ℤ]

/-- The signed difference and sum of a square, with the specified connecting morphism. -/
def shortComplexTriangle (A : Square C) (δ : A.X₄ ⟶ A.X₁⟦(1 : ℤ)⟧) : Triangle C :=
  Triangle.mk A.commSq.shortComplex.f A.commSq.shortComplex.g δ

/-- A square morphism compatible with the connecting morphisms gives a triangle morphism. -/
def shortComplexTriangleMap {A B : Square C} (m : A ⟶ B)
    {δ : A.X₄ ⟶ A.X₁⟦(1 : ℤ)⟧} {ε : B.X₄ ⟶ B.X₁⟦(1 : ℤ)⟧}
    (hδ : δ ≫ m.τ₁⟦(1 : ℤ)⟧' = m.τ₄ ≫ ε) :
    A.shortComplexTriangle δ ⟶ B.shortComplexTriangle ε where
  hom₁ := m.τ₁
  hom₂ := biprod.map m.τ₂ m.τ₃
  hom₃ := m.τ₄
  comm₁ := ((shortComplexFunctor C).map m).comm₁₂.symm
  comm₂ := ((shortComplexFunctor C).map m).comm₂₃.symm
  comm₃ := hδ

end

/-- An additive functor preserving binary biproducts identifies the triangle of the mapped row
with the signed triangle of the mapped square, using the same connecting morphism. -/
def mapShortComplexTriangleIso {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] [HasShift D ℤ]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F] (A : Square C)
    (δ : F.obj A.X₄ ⟶ (F.obj A.X₁)⟦(1 : ℤ)⟧) :
    Triangle.mk (F.map A.commSq.shortComplex.f) (F.map A.commSq.shortComplex.g) δ ≅
      (A.map F).shortComplexTriangle δ := by
  refine Triangle.isoMk _ _ (Iso.refl _) (F.mapBiprod A.X₂ A.X₃) (Iso.refl _) ?_ ?_ ?_
  · change F.map (biprod.lift A.f₁₂ (-A.f₁₃)) ≫ (F.mapBiprod A.X₂ A.X₃).hom =
      𝟙 _ ≫ biprod.lift (F.map A.f₁₂) (-(F.map A.f₁₃))
    rw [biprod.map_lift_mapBiprod F, F.map_neg, Category.id_comp]
  · change F.map (biprod.desc A.f₂₄ A.f₃₄) ≫ 𝟙 _ =
      (F.mapBiprod A.X₂ A.X₃).hom ≫ biprod.desc (F.map A.f₂₄) (F.map A.f₃₄)
    rw [Category.comp_id, biprod.mapBiprod_hom_desc]
  · change δ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ δ
    simp

end CategoryTheory.Square
