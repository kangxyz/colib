/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.Bass.SupportedForget

/-! Original supported negative quotient and actual support-forgetting consumers. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme.Modules

universe u
noncomputable section

example (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Function.Surjective (supportedNegativeKπ A n) := supportedNegativeKπ_surjective A n

example (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    (x : supportedNegativeK (pairLaurentFunctor.obj A) n) :
    supportedNegativeKπ A n x = 0 ↔
      ∃ a b : supportedNegativeK (pairPolynomialFunctor.obj A) n,
        supportedNegativeKPullback (pairPlus.app A) n a -
          supportedNegativeKPullback (pairMinus.app A) n b = x :=
  supportedNegativeKπ_eq_zero_iff A n x

example (A : QuasiCompactOpenPairs.{u}) (n : ℕ) {B : AddCommGrpCat.{u + 1}}
    (f : supportedNegativeK (pairLaurentFunctor.obj A) n ⟶ B)
    (hp : supportedNegativeKPullback (pairPlus.app A) n ≫ f = 0)
    (hm : supportedNegativeKPullback (pairMinus.app A) n ≫ f = 0) :
    ∃! g : supportedNegativeK A (n + 1) ⟶ B, supportedNegativeKπ A n ≫ g = f := by
  exact ⟨supportedNegativeKDesc A n f hp hm, supportedNegativeKπ_desc A n f hp hm,
    fun g hg => supportedNegativeKDesc_unique A n f hp hm g hg⟩

example (A : QuasiCompactOpenPairs.{u}) (a : PerfectSupportedK A.obj.hom 0) :
    supportedNegativeKForget A 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKMap A.obj.hom 0 a) := supportedNegativeKForget_zero A a

example {A B : QuasiCompactOpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    supportedNegativeKPullback f n ≫ supportedNegativeKForget A n =
      supportedNegativeKForget B n ≫ negativeKPullback (quasiCompactOpenPairsBase.map f) n :=
  supportedNegativeKForget_naturality f n

example (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKπ A n ≫ supportedNegativeKForget A (n + 1) =
      supportedNegativeKForget (pairLaurentFunctor.obj A) n ≫
        negativeKπ (quasiCompactOpenPairsBase.obj A) n := supportedNegativeKForget_π A n

end
