module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Basic

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace

universe u

noncomputable section

example {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {R : CommRingCat.{u}} [IsLocalRing R] (p : X ⟶ Spec R)
    (s₀ s₁ : Spec R ⟶ X) (h₀ : s₀ ≫ p = 𝟙 _) (h₁ : s₁ ≫ p = 𝟙 _)
    (hs : s₀ (IsLocalRing.closedPoint R) = s₁ (IsLocalRing.closedPoint R)) :
    ∃ (U : X.Opens) (t₀ t₁ : Spec R ⟶ U.toScheme),
      IsIntegral U.toScheme ∧ IsClosedImmersion U.ι ∧
      t₀ ≫ U.ι = s₀ ∧ t₁ ≫ U.ι = s₁ ∧
      t₀ ≫ U.ι ≫ p = 𝟙 _ ∧ t₁ ≫ U.ι ≫ p = 𝟙 _ := by
  obtain ⟨U, t₀, t₁, -, -, hU, hi, ht₀, ht₁⟩ :=
    exists_integral_component_lifts_of_closedPoint_eq s₀ s₁ hs
  exact ⟨U, t₀, t₁, hU, hi, ht₀, ht₁,
    by rw [← Category.assoc, ht₀, h₀], by rw [← Category.assoc, ht₁, h₁]⟩

#print axioms AlgebraicGeometry.Scheme.exists_integral_component_lifts_of_closedPoint_eq
#print axioms AlgebraicGeometry.Scheme.isIntegral_normalComponentOpen
#print axioms AlgebraicGeometry.Scheme.isClosedImmersion_normalComponentOpen

example {X T : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {R : CommRingCat.{u}} [IsLocalRing R] (g : T ⟶ Spec R) (s₀ s₁ : Spec R ⟶ X)
    (x : X) (h₀ : s₀ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x)
    (h₁ : s₁ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x)
    (hs : g ≫ s₀ = g ≫ s₁) :
    g ≫ liftToNormalComponent s₀ x h₀ = g ≫ liftToNormalComponent s₁ x h₁ :=
  comp_liftToNormalComponent_eq_of_comp_eq g s₀ s₁ x h₀ h₁ hs

#print axioms AlgebraicGeometry.Scheme.comp_liftToNormalComponent_eq_of_comp_eq
