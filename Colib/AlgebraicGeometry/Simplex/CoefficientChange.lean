/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains

/-! # Coefficient change for the literal algebraic singular simplices -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- Applying a coefficient functor commutes with the literal product simplices. -/
def simplicialPresheafWhiskerIso
    {A B : Type*} [Category* A] [Category* B]
    (P : (SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ A) (F : A ⥤ B) :
    ((SimplicialObject.whiskering _ _).obj
      ((Functor.whiskeringRight _ _ _).obj F)).obj (simplicialPresheaf R P) ≅
      simplicialPresheaf R (P ⋙ F) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    ext U
    change F.map (P.map _) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (P.map _)
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicSimplex
