/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback

/-! Actual open-pair K-functor maps, triple composition and the original change-weak square. -/
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

universe u
variable {A B C D : Scheme.OpenPairs.{u}}

example (n : ℕ) :
    (BoundedAboveFlatPerfectOpenKFunctor n).obj (op A) =
      GrpCat.of (BoundedAboveFlatPerfectOpenK A.hom n) := rfl

example (f : A ⟶ B) (n : ℕ) :
    (BoundedAboveFlatPerfectOpenKFunctor n).map f.op =
      GrpCat.ofHom (KMap (boundedAboveFlatPerfectOpenPullback_isExact f) n) := rfl

example (n : ℕ) :
    boundedAboveFlatPerfectOpenKPullback (𝟙 A) n = MonoidHom.id _ :=
  boundedAboveFlatPerfectOpenKPullback_id A n

example (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (n : ℕ) :
    boundedAboveFlatPerfectOpenKPullback (f ≫ g ≫ h) n =
      (boundedAboveFlatPerfectOpenKPullback f n).comp
        ((boundedAboveFlatPerfectOpenKPullback g n).comp
          (boundedAboveFlatPerfectOpenKPullback h n)) := by
  rw [boundedAboveFlatPerfectOpenKPullback_comp, boundedAboveFlatPerfectOpenKPullback_comp]

example (f : A ⟶ B) (g : B ⟶ C) :
    boundedAboveFlatPerfectOpenKPullback (f ≫ g) 0 =
      (boundedAboveFlatPerfectOpenKPullback f 0).comp
        (boundedAboveFlatPerfectOpenKPullback g 0) :=
  boundedAboveFlatPerfectOpenKPullback_comp f g 0

example (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectOpenKPullback f n).comp
        (boundedAboveFlatPerfectOpenKMap B.hom n) =
      (boundedAboveFlatPerfectOpenKMap A.hom n).comp
        (boundedAboveFlatPerfectKPullback f.right n) :=
  boundedAboveFlatPerfectOpenKMap_pullback f n
