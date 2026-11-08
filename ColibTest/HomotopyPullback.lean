/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.HomotopyPullback.QuasiIso
import Colib.Algebra.Homology.DerivedCategory.EqualityDenominators

/-! Regression clients for actual common-denominator homotopies and strict pullback lifts. -/

open CategoryTheory CategoryTheory.Limits CochainComplex

noncomputable section

universe u v d

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B T M : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T)

example (a : M ⟶ A) (b : M ⟶ B) (H : Homotopy (a ≫ f) (b ≫ g)) :
    homotopyPullbackLift f g a b H ≫ homotopyPullbackFst f g = a ∧
      homotopyPullbackLift f g a b H ≫ homotopyPullbackSnd f g = b :=
  ⟨homotopyPullbackLift_fst f g a b H, homotopyPullbackLift_snd f g a b H⟩

example (i : ℤ) : SplitEpi ((homotopyPullbackSnd f g).f i) :=
  homotopyPullbackSndSplitEpi f g i

example [QuasiIso g] : QuasiIso (homotopyPullbackFst f g) :=
  quasiIso_homotopyPullbackFst f g

example [QuasiIso f] : QuasiIso (homotopyPullbackSnd f g) :=
  quasiIso_homotopyPullbackSnd f g

example (a : M ⟶ A) (b : M ⟶ B) (H : Homotopy (a ≫ f) (b ≫ g))
    [QuasiIso g] [QuasiIso a] : QuasiIso (homotopyPullbackLift f g a b H) :=
  quasiIso_homotopyPullbackLift f g a b H

example [HasDerivedCategory.{d} C] {K₁ K₂ L : CochainComplex C ℤ}
    (f₁ g₁ : K₁ ⟶ L) (f₂ g₂ : K₂ ⟶ L)
    (h₁ : DerivedCategory.Q.map f₁ = DerivedCategory.Q.map g₁)
    (h₂ : DerivedCategory.Q.map f₂ = DerivedCategory.Q.map g₂) :
    ∃ (N : CochainComplex C ℤ) (s : L ⟶ N), QuasiIso s ∧
      Nonempty (Homotopy (f₁ ≫ s) (g₁ ≫ s)) ∧
      Nonempty (Homotopy (f₂ ≫ s) (g₂ ≫ s)) :=
  exists_post_quasiIso_two_homotopies_of_derived_eq f₁ g₁ f₂ g₂ h₁ h₂
