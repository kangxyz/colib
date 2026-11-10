/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Equal-degree monic polynomial pencils

The literal polynomial pencil and its coefficient and monicity formulas, extracted
from `Motivic/Aglib/RingTheory/Polynomial/ZeroNeighborhood/Pencil.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`322039276089a1746ecc5c66c7632e77824d6d33`, lines 22-42.

Only these elementary polynomial facts are needed to construct the actual
boundary-one homotopy. Interpolation, finite-free quotient algebras and geometric
zero-section neighborhoods are not prerequisites for this lower layer.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Polynomial.ZeroNeighborhoodInterpolation

variable {R : Type u} [CommRing R]

/-- The inner variable is the homotopy parameter; the outer variable is the target. -/
def pencil (p q : R[X]) : R[X][X] := C (1 - X) * p.map C + C X * q.map C

lemma pencil_coeff (p q : R[X]) (n : ℕ) :
    (pencil p q).coeff n = (1 - X) * C (p.coeff n) + X * C (q.coeff n) := by
  simp only [pencil, coeff_add, coeff_C_mul, coeff_map]

lemma pencil_monic_natDegree [Nontrivial R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) (hdeg : q.natDegree = p.natDegree) :
    (pencil p q).Monic ∧ (pencil p q).natDegree = p.natDegree := by
  have hle : (pencil p q).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [pencil_coeff, coeff_eq_zero_of_natDegree_lt hn,
      coeff_eq_zero_of_natDegree_lt (hdeg ▸ hn)]
    simp
  have hc : (pencil p q).coeff p.natDegree = 1 := by
    rw [pencil_coeff, hp.coeff_natDegree, ← hdeg, hq.coeff_natDegree]
    simp
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hle hc,
    natDegree_eq_of_le_of_coeff_ne_zero hle (hc.trans_ne one_ne_zero)⟩

end Polynomial.ZeroNeighborhoodInterpolation
