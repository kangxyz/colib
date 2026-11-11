/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AlgebraicSimplex.Polynomial
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Actual units of the barycentric simplex over a reduced ring

Native polynomial-unit constancy is transported through the existing explicit
last-coordinate elimination. The forward map remains the actual constant map,
including in degree zero and over the zero ring. No domain or Noetherian premise
is used. This supplies the ring-level producer for the original
`UnitHomotopyInvariance.lean` at motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The actual coefficient map on the barycentric quotient is injective. -/
theorem constant_injective (n : ℕ) : Function.Injective (constant R n) := by
  intro x y h
  apply MvPolynomial.C_injective (Fin n) R
  simpa only [polynomialProjection_constant] using congrArg (polynomialProjection R n) h

variable [IsReduced R]

/-- Every unit of the genuine simplex coordinate ring comes from a scalar unit. -/
theorem units_constant_bijective (n : ℕ) :
    Function.Bijective (Units.map (constant R n).toMonoidHom) := by
  refine ⟨Units.map_injective (constant_injective R n), ?_⟩
  intro v
  have hv : IsUnit (polynomialProjection R n (v : CoordinateRing R n)) :=
    v.isUnit.map (polynomialProjection R n)
  obtain ⟨r, hr, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hv
  obtain ⟨a, rfl⟩ := hr
  refine ⟨a, ?_⟩
  apply Units.ext
  apply (polynomialEquiv R n).injective
  change polynomialProjection R n (constant R n (a : R)) =
    polynomialProjection R n (v : CoordinateRing R n)
  rw [polynomialProjection_constant]
  exact h.symm

/-- The units equivalence is the original scalar map, not a chosen group isomorphism. -/
def constantUnitsEquiv (n : ℕ) : Rˣ ≃* (CoordinateRing R n)ˣ :=
  MulEquiv.ofBijective (Units.map (constant R n).toMonoidHom) (units_constant_bijective R n)

@[simp] theorem constantUnitsEquiv_apply (n : ℕ) (v : Rˣ) :
    constantUnitsEquiv R n v = Units.map (constant R n).toMonoidHom v := rfl

/-- Every simplex operator preserves the scalar units through its actual ring map. -/
theorem pullback_constantUnitsEquiv {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (v : Rˣ) :
    Units.map (pullback R f).toMonoidHom (constantUnitsEquiv R n v) =
      constantUnitsEquiv R m v := by
  apply Units.ext
  exact pullback_constant R f v

end AlgebraicSimplex
