/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Finite products on the smooth site

The identity scheme over the base is terminal. The binary relative products
then give all finite products.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The identity scheme over the base is terminal in the smooth site. -/
def baseIsTerminal (S : Scheme.{u}) : IsTerminal (base S) :=
  IsTerminal.ofUniqueHom (fun X => homMk X.hom (by
    change X.hom ≫ 𝟙 S = X.hom
    exact Category.comp_id _)) (fun X f => by
    apply MorphismProperty.Over.Hom.ext
    change f.left = X.hom
    have h := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 S = X.hom at h
    exact (Category.comp_id _).symm.trans h)

@[simp]
theorem baseIsTerminal_from_left {S : Scheme.{u}} (X : SmoothSite S) :
    ((baseIsTerminal S).from X).left = X.hom :=
  rfl

instance (S : Scheme.{u}) : HasTerminal (SmoothSite S) :=
  (baseIsTerminal S).hasTerminal

instance (S : Scheme.{u}) : HasFiniteProducts (SmoothSite S) :=
  hasFiniteProducts_of_has_binary_and_terminal

end AlgebraicGeometry.Scheme.SmoothSite
