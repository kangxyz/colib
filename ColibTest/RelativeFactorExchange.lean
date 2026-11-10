/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Limits.Pullback.FactorExchange

/-! # Direct consumers of relative first/third factor exchange -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S A B D E : C} (a : A ⟶ S) (b : B ⟶ S) (d : D ⟶ S) (e : E ⟶ S)

example : pullback.fourfoldSwap a b d e ≫ pullback.fourfoldSwap d b a e = 𝟙 _ :=
  pullback.fourfoldSwap_comp a b d e

example : (pullback.fourfoldSwapIso a b d e).hom ≫
    pullback.fourfoldFirst d b a e = pullback.fourfoldThird a b d e :=
  pullback.fourfoldSwap_first a b d e

example : (pullback.fourfoldSwapIso a b d e).hom ≫
    pullback.fourfoldSecond d b a e = pullback.fourfoldSecond a b d e :=
  pullback.fourfoldSwap_second a b d e

example : pullback.diagonal (pullback.fst a b ≫ a) ≫
    (pullback.fourfoldSwapIso a b a b).hom = pullback.diagonal (pullback.fst a b ≫ a) :=
  pullback.diagonal_fourfoldSwap a b
