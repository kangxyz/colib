/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousPrincipalQuadraticParameters

/-! # Same-tuple selection without supplied geometric outputs -/

open MvPolynomial AlgebraicGeometry CategoryTheory QuadraticIncidence

universe u

/-- No good tuple, finite map, or smooth neighborhood is supplied: the coefficients
and one principal neighborhood of the entire marked fiber are actual conclusions. -/
example (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∃ r : R,
        r - 1 ∈ Ideal.map (aeval (R := k) f).toRingHom
          (Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal) ∧
        (∀ Q : PrimeSpectrum R,
          Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
            Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (aeval (R := k) f).toRingHom)) := by
  obtain ⟨a, c, hc, hI, hinfinity, _, r, hr, hfiber, haffine, hsmooth⟩ :=
    exists_simultaneous_principal_quadratic_parameters k R P I hI g hg d hd q hq
  exact ⟨a, c, hc, hI, hinfinity, r, hr, hfiber, haffine, hsmooth⟩

/-- The zero-dimensional curve base is covered without adding a positivity
hypothesis, and the extra row is still chosen in the original coefficient field. -/
example (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (hd : Algebra.trdeg k R = 1) :
    ∃ (a : Exponent σ → k) (c : Fin 0 × Exponent σ → k),
      InfinityChart.NoCommonInfinityZero k R g 0 (prependParameters k 0 a c) := by
  obtain ⟨a, c, _, _, hinfinity, _⟩ :=
    exists_simultaneous_principal_quadratic_parameters k R P ⊤ top_ne_bot
      g hg 0 (by simpa using hd) 1 one_ne_zero
  exact ⟨a, c, hinfinity⟩
