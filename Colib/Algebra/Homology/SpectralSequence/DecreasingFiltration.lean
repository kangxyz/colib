/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# Spectral sequences of decreasing filtrations

The order homomorphism `t : ℤ →o ι` indexes a decreasing filtration by `Fᵖ = F (t (-p))`.
The first page uses the successive pieces at `t (-p - 1) ≤ t (-p)` in total degree `p + q`.
The differential on page `r` has bidegree `(r, 1 - r)`.
-/

@[expose] public section

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type*} [Preorder ι] (t : ℤ →o ι)

/-- The data for the cohomological spectral sequence of a decreasing filtration,
starting on page `1`. -/
@[simps]
def coreE₁DecreasingFiltration :
    SpectralSequenceDataCore ι (fun r ↦ ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := t (-pq.1 - r)
  i₁ pq := t (-pq.1 - 1)
  i₂ pq := t (-pq.1)
  i₃ r pq _ := t (-pq.1 + r - 1)
  le₀₁ r pq hr := t.monotone (by lia)
  le₁₂ pq := t.monotone (by lia)
  le₂₃ r pq hr := t.monotone (by lia)
  hc := by
    rintro r pq _ rfl _
    change pq.1 + pq.2 + 1 = (pq.1 + r) + (pq.2 + (1 - r))
    lia
  hc₀₂ := by
    rintro r pq _ rfl _
    exact congrArg t (show -pq.1 - r = -(pq.1 + r) by lia)
  hc₁₃ := by
    rintro r pq _ rfl _
    exact congrArg t (show -pq.1 - 1 = -(pq.1 + r) + r - 1 by lia)
  antitone_i₀ r r' pq hr hrr' := t.monotone (by lia)
  monotone_i₃ r r' pq hr hrr' := t.monotone (by lia)
  i₀_prev := by
    rintro r r' pq _ rfl hrr' _
    exact congrArg t (show -pq.1 - r' = -(pq.1 + r) - 1 by lia)
  i₃_next := by
    rintro r r' pq _ rfl hrr' _
    exact congrArg t (show -(pq.1 + r) + r' - 1 = -pq.1 by lia)

instance {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C ι) :
    X.HasSpectralSequence (coreE₁DecreasingFiltration t) where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr :=
    (hpq (pq + (r, 1 - r)) rfl).elim
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr :=
    (hpq (pq - (r, 1 - r)) (by change pq - (r, 1 - r) + (r, 1 - r) = pq; simp)).elim

instance : (coreE₁DecreasingFiltration t).HasFirstPageComputation where
  hi₀₁ pq := rfl
  hi₂₃ pq := congrArg t (show -pq.1 = -pq.1 + 1 - 1 by lia)

end CategoryTheory.Abelian.SpectralObject
