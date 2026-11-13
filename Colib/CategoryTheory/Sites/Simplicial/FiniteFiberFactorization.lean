/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Filtered.FinallySmall

/-!
# Finite simplicial maps into a site fiber

Finite simplicial maps into the original fiber come from one site
neighborhood. The chosen small filtered model is used only to apply
finite presentability, and the resulting map has its original germ.
This is a finite support step in Jardine, *Simplicial presheaves*,
Lemma 2.4, pp. 65–66. https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}

/-- A map from a finite simplicial set into an actual site fiber factors
through an original neighborhood value of the presheaf. -/
theorem exists_toPresheafFiber_factorization_of_finite
    (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ SSet.{w}) {K : SSet.{w}} [K.Finite]
    (f : K ⟶ Φ.presheafFiber.obj P) :
    ∃ (U : C) (x : Φ.fiber.obj U) (g : K ⟶ P.obj (op U)),
      g ≫ Φ.toPresheafFiber U x P = f := by
  let E := FinallySmall.fromFilteredFinalModel.{w} Φ.fiber.Elementsᵒᵖ
  let c := Φ.presheafFiberCocone P
  let : E.Final := inferInstanceAs
    (FinallySmall.fromFilteredFinalModel.{w} Φ.fiber.Elementsᵒᵖ).Final
  have hc : IsColimit (c.whisker E) :=
    (Functor.Final.isColimitWhiskerEquiv E c).symm (Φ.isColimitPresheafFiberCocone P)
  obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc f
  exact ⟨(E.obj i).unop.1, (E.obj i).unop.2, g, hg⟩

end CategoryTheory.GrothendieckTopology.Point
