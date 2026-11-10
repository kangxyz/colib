/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Pointed presheaf pushouts of commutative squares

For a square in a category, the pointed Yoneda images of its top and left
arrows have an actual categorical pushout. The other two arrows induce a
map from that pushout to the pointed representable of the fourth corner.
This map is natural in morphisms of squares. These are strict colimit
constructions; no local or homotopical equivalence is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- The strict pushout of the top and left pointed representable maps. -/
def squarePushout (sq : Square C) : PointedSimplicialPresheaf.{v} C :=
  pushout ((yoneda C).map sq.f₁₂) ((yoneda C).map sq.f₁₃)

/-- The top-right pointed representable maps to the strict pushout. -/
def squarePushoutInl (sq : Square C) : (yoneda C).obj sq.X₂ ⟶ squarePushout C sq :=
  pushout.inl _ _

/-- The bottom-left pointed representable maps to the strict pushout. -/
def squarePushoutInr (sq : Square C) : (yoneda C).obj sq.X₃ ⟶ squarePushout C sq :=
  pushout.inr _ _

@[reassoc]
theorem squarePushout_condition (sq : Square C) :
    (yoneda C).map sq.f₁₂ ≫ squarePushoutInl C sq =
      (yoneda C).map sq.f₁₃ ≫ squarePushoutInr C sq :=
  pushout.condition

/-- The displayed strict pointed presheaf square is a categorical pushout. -/
theorem squarePushout_isPushout (sq : Square C) :
    IsPushout ((yoneda C).map sq.f₁₂) ((yoneda C).map sq.f₁₃)
      (squarePushoutInl C sq) (squarePushoutInr C sq) :=
  IsPushout.of_hasPushout _ _

/-- The map from the strict pushout to the pointed fourth corner. -/
def squarePushoutMap (sq : Square C) : squarePushout C sq ⟶ (yoneda C).obj sq.X₄ :=
  pushout.desc ((yoneda C).map sq.f₂₄) ((yoneda C).map sq.f₃₄)
    (by rw [← Functor.map_comp, ← Functor.map_comp, sq.fac])

@[reassoc (attr := simp)]
theorem squarePushoutInl_map (sq : Square C) :
    squarePushoutInl C sq ≫ squarePushoutMap C sq = (yoneda C).map sq.f₂₄ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem squarePushoutInr_map (sq : Square C) :
    squarePushoutInr C sq ≫ squarePushoutMap C sq = (yoneda C).map sq.f₃₄ :=
  pushout.inr_desc _ _ _

/-- A morphism of squares induces the map on their strict pointed pushouts. -/
def squarePushoutHom {sq sq' : Square C} (φ : sq ⟶ sq') :
    squarePushout C sq ⟶ squarePushout C sq' :=
  pushout.map ((yoneda C).map sq.f₁₂) ((yoneda C).map sq.f₁₃)
    ((yoneda C).map sq'.f₁₂) ((yoneda C).map sq'.f₁₃)
    ((yoneda C).map φ.τ₂) ((yoneda C).map φ.τ₃) ((yoneda C).map φ.τ₁)
    (by rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂])
    (by rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₃])

@[reassoc (attr := simp)]
theorem squarePushoutInl_hom {sq sq' : Square C} (φ : sq ⟶ sq') :
    squarePushoutInl C sq ≫ squarePushoutHom C φ =
      (yoneda C).map φ.τ₂ ≫ squarePushoutInl C sq' :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem squarePushoutInr_hom {sq sq' : Square C} (φ : sq ⟶ sq') :
    squarePushoutInr C sq ≫ squarePushoutHom C φ =
      (yoneda C).map φ.τ₃ ≫ squarePushoutInr C sq' :=
  pushout.inr_desc _ _ _

@[simp]
theorem squarePushoutHom_id (sq : Square C) :
    squarePushoutHom C (𝟙 sq) = 𝟙 (squarePushout C sq) := by
  apply pushout.hom_ext
  · change squarePushoutInl C sq ≫ _ = squarePushoutInl C sq ≫ _
    rw [squarePushoutInl_hom]
    change (yoneda C).map (𝟙 sq.X₂) ≫ _ = _
    simp
  · change squarePushoutInr C sq ≫ _ = squarePushoutInr C sq ≫ _
    rw [squarePushoutInr_hom]
    change (yoneda C).map (𝟙 sq.X₃) ≫ _ = _
    simp

theorem squarePushoutHom_comp {sq₁ sq₂ sq₃ : Square C}
    (φ : sq₁ ⟶ sq₂) (ψ : sq₂ ⟶ sq₃) :
    squarePushoutHom C (φ ≫ ψ) = squarePushoutHom C φ ≫ squarePushoutHom C ψ := by
  apply pushout.hom_ext
  · change squarePushoutInl C sq₁ ≫ _ = squarePushoutInl C sq₁ ≫ _
    rw [squarePushoutInl_hom, squarePushoutInl_hom_assoc, squarePushoutInl_hom]
    change (yoneda C).map (φ.τ₂ ≫ ψ.τ₂) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
  · change squarePushoutInr C sq₁ ≫ _ = squarePushoutInr C sq₁ ≫ _
    rw [squarePushoutInr_hom, squarePushoutInr_hom_assoc, squarePushoutInr_hom]
    change (yoneda C).map (φ.τ₃ ≫ ψ.τ₃) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]

/-- The strict pushout map is natural in the entire commutative square. -/
@[reassoc]
theorem squarePushoutMap_naturality {sq sq' : Square C} (φ : sq ⟶ sq') :
    squarePushoutHom C φ ≫ squarePushoutMap C sq' =
      squarePushoutMap C sq ≫ (yoneda C).map φ.τ₄ := by
  apply pushout.hom_ext
  · change squarePushoutInl C sq ≫ _ = squarePushoutInl C sq ≫ _
    rw [squarePushoutInl_hom_assoc, squarePushoutInl_map,
      squarePushoutInl_map_assoc, ← Functor.map_comp, ← Functor.map_comp, φ.comm₂₄]
  · change squarePushoutInr C sq ≫ _ = squarePushoutInr C sq ≫ _
    rw [squarePushoutInr_hom_assoc, squarePushoutInr_map,
      squarePushoutInr_map_assoc, ← Functor.map_comp, ← Functor.map_comp, φ.comm₃₄]

/-- The strict pointed pushout as a functor of commutative squares. -/
def squarePushoutFunctor : Square C ⥤ PointedSimplicialPresheaf.{v} C where
  obj := squarePushout C
  map := squarePushoutHom C
  map_id := squarePushoutHom_id C
  map_comp := squarePushoutHom_comp C

/-- The canonical strict pushout maps form a natural transformation. -/
def squarePushoutNatTrans : squarePushoutFunctor C ⟶ Square.evaluation₄ ⋙ yoneda C where
  app := squarePushoutMap C
  naturality _ _ φ := squarePushoutMap_naturality C φ

end CategoryTheory.PointedSimplicialPresheaf
