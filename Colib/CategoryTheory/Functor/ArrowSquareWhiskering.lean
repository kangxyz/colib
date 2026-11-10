/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Colib.Util.References

/-! Strict precomposition interchange for the original double-arrow diagram construction. -/
@[expose] public section
noncomputable section
namespace CategoryTheory.Functor

universe uC vC uD vD uE vE

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]

/-- Restricting a strict square diagram commutes with its native double-arrow evaluation
and arbitrary postcomposition, as an equality of functors rather than an isomorphism. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictUnderDiagram.lean:29-33" "generalization"
  "Generic strict functor interchange underlying restriction of the original Laurent construction"]
theorem whiskeringLeft_comp_mapArrowSquare
    (L : C ⥤ D)
    (QC : C ⥤ Arrow (Arrow C))
    (QD : D ⥤ Arrow (Arrow D))
    (K : Arrow (Arrow E) ⥤ E)
    (h : QC ⋙ L.mapArrow.mapArrow = L ⋙ QD) :
    (Functor.whiskeringLeft C D E).obj L ⋙
      (Functor.mapArrowFunctor C E ⋙
        Functor.mapArrowFunctor (Arrow C) (Arrow E) ⋙
        (Functor.whiskeringLeft C (Arrow (Arrow C))
          (Arrow (Arrow E))).obj QC ⋙
        (Functor.whiskeringRight C (Arrow (Arrow E)) E).obj K) =
      (Functor.mapArrowFunctor D E ⋙
        Functor.mapArrowFunctor (Arrow D) (Arrow E) ⋙
        (Functor.whiskeringLeft D (Arrow (Arrow D))
          (Arrow (Arrow E))).obj QD ⋙
        (Functor.whiskeringRight D (Arrow (Arrow E)) E).obj K) ⋙
      (Functor.whiskeringLeft C D E).obj L := by
  calc
    _ = Functor.mapArrowFunctor D E ⋙
          Functor.mapArrowFunctor (Arrow D) (Arrow E) ⋙
          (Functor.whiskeringLeft C (Arrow (Arrow D))
            (Arrow (Arrow E))).obj (QC ⋙ L.mapArrow.mapArrow) ⋙
          (Functor.whiskeringRight C (Arrow (Arrow E)) E).obj K := rfl
    _ = Functor.mapArrowFunctor D E ⋙
          Functor.mapArrowFunctor (Arrow D) (Arrow E) ⋙
          (Functor.whiskeringLeft C (Arrow (Arrow D))
            (Arrow (Arrow E))).obj (L ⋙ QD) ⋙
          (Functor.whiskeringRight C (Arrow (Arrow E)) E).obj K := by
      rw [h]
    _ = _ := rfl

end CategoryTheory.Functor
