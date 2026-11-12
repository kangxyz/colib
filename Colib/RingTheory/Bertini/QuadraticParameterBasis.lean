/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-! # Fixed original quadratic monomial and row bases

Only the basis declarations are extracted from the original incidence files.
No incidence-coordinate quotient or geometric rank theorem is assumed here.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial Module
universe u v w z
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

@[simp]
theorem monomialBasis_coe (A : Type w) [CommRing A] (σ : Type z) (q : Exponent σ) :
    ((monomialBasis A σ) q).val = monomial q.val 1 := by
  classical
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := A)
      {e : σ →₀ ℕ | e.sum (fun _ n => n) ≤ 2}).symm (Finsupp.single q 1)).val) = _
  exact congrArg (fun f : (σ →₀ ℕ) →₀ A => (AddMonoidAlgebra.ofCoeff f : MvPolynomial σ A))
    (Finsupp.supportedEquivFinsupp_symm_single _ q 1)


/-- One fixed monomial coordinate basis for all projection coordinates. -/
def parameterBasis (A : Type w) [CommRing A] (σ : Type z) (d : ℕ) :
    Basis (Fin d × Exponent σ) A (Fin d → restrictTotalDegree σ A 2) :=
  (Pi.basis fun _ : Fin d => monomialBasis A σ).reindex
    (Equiv.sigmaEquivProd (Fin d) (Exponent σ))

@[simp]
theorem parameterBasis_apply (A : Type w) [CommRing A] (σ : Type z) (d : ℕ)
    (q : Fin d × Exponent σ) :
    parameterBasis A σ d q = Pi.single q.1 (monomialBasis A σ q.2) := by
  simp [parameterBasis, Basis.reindex_apply]

end QuadraticIncidence
