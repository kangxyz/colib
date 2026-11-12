/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicLocalization

/-! # Original empty-support and same-time basic localization regressions -/
@[expose] public section
noncomputable section
open Topology CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules GlobalSectionChangeIndex GlobalSupportedSection
  ParameterAuxiliarySupport
namespace ColibTest.OriginalNormalizedBasicLocalization
universe u

private theorem composite_square {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ F) (e : F ⟶ E)
    (f : A ⟶ F) (hb : b ≫ c = d ≫ e) (ha : a ≫ d = f) :
    (a ≫ b) ≫ c = f ≫ e := by
  rw [Category.assoc, hb, ← Category.assoc, ha]

/-- Both actual normalized arrows compose through the unchanged support-forget map. -/
theorem composite_forget {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    (normalizedPresentationEnlargement f T X ≫ normalizedPresentationRestriction f T X) ≫
        ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X =
      ParameterTensorNormalizedRowPresentation.forget (unionOpen f T).ι X ≫
        ParameterNormalizedBasicLocalization.restriction f X := by
  exact composite_square _ _ _ _ _ _
    (ParameterNormalizedBasicLocalization.restriction_forget f T X)
    (ParameterNormalizedBasicLocalization.enlargement_forget f T X)

/-- A client can compare any original auxiliary-null point at its unchanged time. -/
theorem prescribed_null_time (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (x : (normalizedFiberPresentation U.ι ⊥ X).space n) :
    (ParameterNormalizedBasicLocalization.basicNull Q U X).level n
        (r, (ParameterNormalizedBasicLocalization.basicSourceIso Q U X).hom.map n x) =
      (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X).map n
        ((normalizedPresentationNull U.ι ⊥ X).level n (r, x)) :=
  (ParameterNormalizedBasicLocalization.basicNull_comparison Q U X n r x).symm

end ColibTest.OriginalNormalizedBasicLocalization
