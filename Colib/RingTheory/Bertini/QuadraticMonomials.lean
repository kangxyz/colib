/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # The original quadratic monomial coefficient space

The coefficient indices and basis are retained from the archived quadratic
incidence construction, independently of its value and differential equations.
-/

@[expose] public noncomputable section

open MvPolynomial Module

universe w z

namespace QuadraticIncidence

/-- Quadratic monomials have an index set independent of the coefficient ring. -/
abbrev Exponent (σ : Type z) := {e : σ →₀ ℕ // e.sum (fun _ n => n) ≤ 2}

instance {σ : Type z} [Finite σ] : Finite (Exponent σ) := by
  let b : Basis (Exponent σ) ℚ (restrictTotalDegree σ ℚ 2) := basisRestrictSupport ℚ _
  exact Module.Finite.finite_basis b

instance {σ : Type z} [Finite σ] : Fintype (Exponent σ) := Fintype.ofFinite _

/-- The original monomial basis of the quadratic parameter module. -/
def monomialBasis (A : Type w) [CommRing A] (σ : Type z) :
    Basis (Exponent σ) A (restrictTotalDegree σ A 2) := basisRestrictSupport A _

end QuadraticIncidence
