/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Scheme stalk maps at a specified image point

For a commutative square, its two composites can present the same image
point by different expressions. Transport along this point equality
before applying the actual stalk map. The transported maps compose
contravariantly and respect equality of the original scheme maps.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A B C : Scheme.{u}}

/-- The literal stalk map with its source written at an equal image point. -/
def stalkMapAtImage (f : A ⟶ B) (x : A) (y : B) (h : y = f x) :
    B.presheaf.stalk y ⟶ A.presheaf.stalk x :=
  (B.presheaf.stalkCongr (.of_eq h)).hom ≫ f.stalkMap x

@[simp]
theorem stalkMapAtImage_rfl (f : A ⟶ B) (x : A) :
    f.stalkMapAtImage x (f x) rfl = f.stalkMap x := by
  simp only [stalkMapAtImage, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- Point transports cancel when the two actual stalk maps compose. -/
@[reassoc]
theorem stalkMapAtImage_comp (f : A ⟶ B) (g : B ⟶ C)
    (x : A) (y : B) (z : C) (hy : y = f x) (hz : z = g y) :
    g.stalkMapAtImage y z hz ≫ f.stalkMapAtImage x y hy =
      (f ≫ g).stalkMapAtImage x z (hz.trans (congrArg g hy)) := by
  subst y
  subst z
  simp only [stalkMapAtImage_rfl]
  change g.stalkMap (f x) ≫ f.stalkMap x =
    (f ≫ g).stalkMapAtImage x ((f ≫ g) x) rfl
  rw [stalkMapAtImage_rfl, Scheme.Hom.stalkMap_comp]

/-- Changing the displayed image point before the transported map gives the
single transport from the new point. -/
@[reassoc]
theorem stalkMapAtImage_precomp_cast (f : A ⟶ B) (x : A)
    (y z : B) (hy : y = f x) (hz : z = y) :
    (B.presheaf.stalkCongr (.of_eq hz)).hom ≫ f.stalkMapAtImage x y hy =
      f.stalkMapAtImage x z (hz.trans hy) := by
  subst z
  simp only [TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- Equal original morphisms give the same stalk map at the specified point. -/
theorem stalkMapAtImage_congr (f g : A ⟶ B) (h : f = g)
    (x : A) (y : B) (hf : y = f x) (hg : y = g x) :
    f.stalkMapAtImage x y hf = g.stalkMapAtImage x y hg := by
  subst g
  rfl

end AlgebraicGeometry.Scheme.Hom
