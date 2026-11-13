/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Shift-compatible natural transformations on triangles

A natural transformation between the original shift-commuting
functors induces a morphism of their actual images of every triangle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated
open CategoryTheory.Limits

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]

/-- Apply a shift-compatible natural transformation to all three
components of the original triangle. -/
@[simps hom₁ hom₂ hom₃]
def mapTriangleHom (τ : F ⟶ G) [CommShift τ ℤ] (T : Triangle C) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := τ.app T.obj₁
  hom₂ := τ.app T.obj₂
  hom₃ := τ.app T.obj₃
  comm₁ := τ.naturality T.mor₁
  comm₂ := τ.naturality T.mor₂
  comm₃ := by
    symm
    change τ.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁ =
      (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (shiftFunctor D (1 : ℤ)).map (τ.app T.obj₁)
    calc
      _ = (τ.app T.obj₃ ≫ G.map T.mor₃) ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
        (Category.assoc _ _ _).symm
      _ = F.map T.mor₃ ≫ τ.app (T.obj₁⟦(1 : ℤ)⟧) ≫
          (G.commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
        (congrArg (· ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
          (τ.naturality T.mor₃).symm).trans (Category.assoc _ _ _)
      _ = _ :=
        (congrArg (F.map T.mor₃ ≫ ·)
          (NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁).symm).trans (Category.assoc _ _ _).symm

end CategoryTheory.NatTrans

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {A : C ⥤ C} [A.CommShift ℤ] {L : C ⥤ D} [L.CommShift ℤ] {G : D ⥤ D} [G.CommShift ℤ]

/-- A shift-compatible transformation between composites gives a morphism
between the successive images of a triangle. -/
def mapComposedTriangleHom (τ : A ⋙ L ⟶ L ⋙ G) [CommShift τ ℤ] (T : Triangle C) :
    L.mapTriangle.obj (A.mapTriangle.obj T) ⟶ G.mapTriangle.obj (L.mapTriangle.obj T) :=
  (Functor.mapTriangleCompIso A L).inv.app T ≫ τ.mapTriangleHom T ≫
    (Functor.mapTriangleCompIso L G).hom.app T

theorem mapComposedTriangleHom_hom₁
    (τ : A ⋙ L ⟶ L ⋙ G) [CommShift τ ℤ] (T : Triangle C) :
    (τ.mapComposedTriangleHom T).hom₁ = τ.app T.obj₁ := by
  change 𝟙 _ ≫ τ.app T.obj₁ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

theorem mapComposedTriangleHom_hom₂
    (τ : A ⋙ L ⟶ L ⋙ G) [CommShift τ ℤ] (T : Triangle C) :
    (τ.mapComposedTriangleHom T).hom₂ = τ.app T.obj₂ := by
  change 𝟙 _ ≫ τ.app T.obj₂ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

theorem mapComposedTriangleHom_hom₃
    (τ : A ⋙ L ⟶ L ⋙ G) [CommShift τ ℤ] (T : Triangle C) :
    (τ.mapComposedTriangleHom T).hom₃ = τ.app T.obj₃ := by
  change 𝟙 _ ≫ τ.app T.obj₃ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A shifted triangle has distinguished image if the unshifted triangle does. -/
theorem mapTriangle_shift_distinguished (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    (s : ℤ) (T : Triangle C) (h : F.mapTriangle.obj T ∈ distTriang D) :
    F.mapTriangle.obj ((Triangle.shiftFunctor C s).obj T) ∈ distTriang D :=
  isomorphic_distinguished _ ((F.mapTriangle.obj T).shift_distinguished h s) _
    ((F.mapTriangleCommShiftIso s).app T)

end CategoryTheory.Functor
