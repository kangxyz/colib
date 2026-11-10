/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Intersection.SmoothSectionCommonList

/-! # Direct actual-stalk consumers with an arbitrary base-change morphism -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

example {S T X : Scheme.{u}} (p : T ⟶ S) [Smooth p]
    (σ : S ⟶ T) (hσ : σ ≫ p = 𝟙 S) (f : X ⟶ S)
    [IsLocallyNoetherian X] (z : pullback (C := Scheme) p f) (s : S)
    (hz : pullback.fst p f z = σ s) :
    ∃ (r : ℕ) (b : Fin r → T.presheaf.stalk (pullback.fst p f z)),
      IsRegular (T.presheaf.stalk (pullback.fst p f z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        ((T.presheaf.stalkCongr (.of_eq hz)).hom ≫ σ.stalkMap s).hom ∧
      IsRegular ((pullback p f).presheaf.stalk z)
        (List.ofFn (fun i => ((pullback.fst p f).stalkMap z).hom (b i))) :=
  Scheme.Hom.exists_isRegular_stalkList_pullback_of_smooth_section p σ hσ f z s hz

example {S T : Scheme.{u}} (p : T ⟶ S) [Smooth p]
    (σ : S ⟶ T) (hσ : σ ≫ p = 𝟙 S) (s : S) :
    let A := S.presheaf.stalk (p (σ s))
    let B := T.presheaf.stalk (σ s)
    letI : Algebra A B := (p.stalkMap (σ s)).hom.toAlgebra
    ∃ (r : ℕ) (b : Fin r → B), IsRegular B (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker (σ.stalkMap s).hom ∧
      Module.Flat A (B ⧸ Ideal.span (Set.range b)) := by
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using
    Scheme.Hom.exists_isRegular_stalkList_flatQuotient_of_smooth_section p σ hσ s (σ s) rfl
