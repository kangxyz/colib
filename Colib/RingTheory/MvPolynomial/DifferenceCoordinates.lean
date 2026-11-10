/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Tactic.FinCases

/-!
# Difference coordinates on three polynomial factors

The change of coordinates `(t₁, t₂, t₃) ↦ (t₁ - t₂, t₂ - t₃, t₃)` is an
algebra automorphism over any commutative coefficient ring. The inverse sends
`(u, v, t)` to `(u + v + t, v + t, t)`. All three coordinate families have the
same arbitrary index type; no finiteness or nontriviality hypothesis is needed.

The generator equations are the polynomial input for the simplex exterior
incidence calculation. They do not assert a Tor or correspondence comparison.
-/

@[expose] public noncomputable section

universe u v

namespace MvPolynomial

variable (R : Type u) [CommRing R] (σ : Type v)

/-- Substitute the two successive differences and the last coordinate family. -/
def tripleDifferenceHom :
    MvPolynomial (Fin 3 × σ) R →ₐ[R] MvPolynomial (Fin 3 × σ) R :=
  aeval fun p => match p with
    | (0, i) => X (0, i) - X (1, i)
    | (1, i) => X (1, i) - X (2, i)
    | (2, i) => X (2, i)

/-- Recover the original coordinates from the two differences and the last family. -/
def tripleSumHom :
    MvPolynomial (Fin 3 × σ) R →ₐ[R] MvPolynomial (Fin 3 × σ) R :=
  aeval fun p => match p with
    | (0, i) => X (0, i) + X (1, i) + X (2, i)
    | (1, i) => X (1, i) + X (2, i)
    | (2, i) => X (2, i)

/-- The coordinate substitution taking the three variable families to their two successive
differences and the last family. Its inverse is the corresponding successive-sum substitution. -/
def tripleDifferenceEquiv :
    MvPolynomial (Fin 3 × σ) R ≃ₐ[R] MvPolynomial (Fin 3 × σ) R :=
  AlgEquiv.ofAlgHom (tripleDifferenceHom R σ) (tripleSumHom R σ)
    (by
      apply algHom_ext
      rintro ⟨j, i⟩
      fin_cases j <;>
        simp [tripleDifferenceHom, tripleSumHom, AlgHom.comp_apply])
    (by
      apply algHom_ext
      rintro ⟨j, i⟩
      fin_cases j <;>
        simp [tripleDifferenceHom, tripleSumHom, AlgHom.comp_apply])

@[simp]
theorem tripleDifferenceEquiv_C (r : R) :
    tripleDifferenceEquiv R σ (C r) = C r := by
  change tripleDifferenceHom R σ (C r) = _
  simp [tripleDifferenceHom]

@[simp]
theorem tripleDifferenceEquiv_X_zero (i : σ) :
    tripleDifferenceEquiv R σ (X (0, i)) = X (0, i) - X (1, i) := by
  change tripleDifferenceHom R σ (X (0, i)) = _
  simp [tripleDifferenceHom]

@[simp]
theorem tripleDifferenceEquiv_X_one (i : σ) :
    tripleDifferenceEquiv R σ (X (1, i)) = X (1, i) - X (2, i) := by
  change tripleDifferenceHom R σ (X (1, i)) = _
  simp [tripleDifferenceHom]

@[simp]
theorem tripleDifferenceEquiv_X_two (i : σ) :
    tripleDifferenceEquiv R σ (X (2, i)) = X (2, i) := by
  change tripleDifferenceHom R σ (X (2, i)) = _
  simp [tripleDifferenceHom]

@[simp]
theorem tripleDifferenceEquiv_symm_C (r : R) :
    (tripleDifferenceEquiv R σ).symm (C r) = C r := by
  change tripleSumHom R σ (C r) = _
  simp [tripleSumHom]

@[simp]
theorem tripleDifferenceEquiv_symm_X_zero (i : σ) :
    (tripleDifferenceEquiv R σ).symm (X (0, i)) = X (0, i) + X (1, i) + X (2, i) := by
  change tripleSumHom R σ (X (0, i)) = _
  simp [tripleSumHom]

@[simp]
theorem tripleDifferenceEquiv_symm_X_one (i : σ) :
    (tripleDifferenceEquiv R σ).symm (X (1, i)) = X (1, i) + X (2, i) := by
  change tripleSumHom R σ (X (1, i)) = _
  simp [tripleSumHom]

@[simp]
theorem tripleDifferenceEquiv_symm_X_two (i : σ) :
    (tripleDifferenceEquiv R σ).symm (X (2, i)) = X (2, i) := by
  change tripleSumHom R σ (X (2, i)) = _
  simp [tripleSumHom]

/-- The first equality-of-parameters equation becomes an original variable in difference
coordinates. -/
@[simp]
theorem tripleDifferenceEquiv_symm_sub_zero_one (i : σ) :
    (tripleDifferenceEquiv R σ).symm (X (0, i) - X (1, i)) = X (0, i) := by
  rw [← tripleDifferenceEquiv_X_zero, AlgEquiv.symm_apply_apply]

/-- The second equality-of-parameters equation becomes the other original difference variable. -/
@[simp]
theorem tripleDifferenceEquiv_symm_sub_one_two (i : σ) :
    (tripleDifferenceEquiv R σ).symm (X (1, i) - X (2, i)) = X (1, i) := by
  rw [← tripleDifferenceEquiv_X_one, AlgEquiv.symm_apply_apply]

end MvPolynomial
