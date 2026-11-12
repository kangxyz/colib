/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.Bass.NegativeGroups

/-! Original genuine Bass quotient consumers, without a stable-homotopy redefinition. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.RingedSpace

universe u

noncomputable section

local instance (X : QuasiCompactSchemes.{u}) :
    CommGroup ((perfectComplexesWaldhausen X.obj.toRingedSpace).K 0) :=
  CategoryTheory.Waldhausen.Additivity.KCommGroup
    (perfectComplexesWaldhausen X.obj.toRingedSpace) 0

-- Degree zero and arbitrary pullbacks are the original perfect K-zero groups and maps.
example (X : QuasiCompactSchemes.{u}) :
    negativeK X 0 = AddCommGrpCat.of
      (Additive ((perfectComplexesWaldhausen X.obj.toRingedSpace).K 0)) := rfl

example {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y)
    (a : (perfectComplexesWaldhausen Y.obj.toRingedSpace).K 0) :
    negativeKPullback f 0 (Additive.ofMul a) =
      Additive.ofMul (perfectKPullback f.hom 0 a) := negativeKPullback_zero f a

-- Every next degree is represented by the actual Laurent group.
example (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Surjective (negativeKπ X n) := negativeKπ_surjective X n

-- The exact original two-chart relation, not a chosen presentation equivalence.
example (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (x : negativeK (PolynomialLaurent.Relative.laurentFunctor.obj X) n) :
    negativeKπ X n x = 0 ↔ ∃ a b : negativeK
      (PolynomialLaurent.Relative.polynomialFunctor.obj X) n,
      negativeKPullback (PolynomialLaurent.Relative.plus.app X) n a -
        negativeKPullback (PolynomialLaurent.Relative.minus.app X) n b = x :=
  negativeKπ_eq_zero_iff X n x

-- Prescribed chart-annihilating maps have exactly one descent on the actual quotient.
example (X : QuasiCompactSchemes.{u}) (n : ℕ) {A : AddCommGrpCat.{u + 1}}
    (f : negativeK (PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶ A)
    (hp : negativeKPullback (PolynomialLaurent.Relative.plus.app X) n ≫ f = 0)
    (hm : negativeKPullback (PolynomialLaurent.Relative.minus.app X) n ≫ f = 0) :
    ∃! g : negativeK X (n + 1) ⟶ A, negativeKπ X n ≫ g = f := by
  exact ⟨negativeKDesc X n f hp hm, negativeKπ_desc X n f hp hm,
    fun g hg => negativeKDesc_unique X n f hp hm g hg⟩

end
