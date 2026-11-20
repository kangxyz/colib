/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Cohomological spectral sequences supported on one row

If the first page is supported on row zero, all pages are supported on row zero.
The differentials vanish from page two onward, and the page transition isomorphisms
identify every later page term with the corresponding term of page two.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits

variable {C : Type*} [Category* C] [Abelian C]
  (E : CohomologicalSpectralSequence C 1)
  (hRow : ∀ pq : ℤ × ℤ, pq.2 ≠ 0 → IsZero ((E.page 1).X pq))

include hRow

lemma isZero_page_X_of_ne_zero_row (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) (hq : pq.2 ≠ 0) :
    IsZero ((E.page r).X pq) :=
  Int.leInduction (motive := fun r hr ↦ IsZero ((E.page r hr).X pq)) (hRow pq hq)
    (fun s hs ih ↦ Limits.IsZero.of_iso
      (((E.page s hs).sc pq).isZero_homology_of_isZero_X₂ ih) (E.iso s (s + 1) pq rfl hs).symm)
    r hr

lemma page_d_eq_zero_of_single_row (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    (E.page r).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
  · by_cases hq : pq.2 = 0
    · have heq : pq.2 + (1 - r) = pq'.2 := congrArg (fun x : ℤ × ℤ ↦ x.2) hrel
      exact (E.isZero_page_X_of_ne_zero_row hRow r (by lia) pq' (by lia)).eq_of_tgt _ _
    · exact (E.isZero_page_X_of_ne_zero_row hRow r (by lia) pq hq).eq_of_src _ _
  · exact (E.page r).shape pq pq' hrel

/-- The page transition at `r ≥ 2` identifies the next page term with the current
term through the homology of two zero differentials. -/
noncomputable def pageSuccXIsoOfSingleRow (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (E.page (r + 1)).X pq ≅ (E.page r).X pq :=
  (E.iso r (r + 1) pq).symm ≪≫
    (ShortComplex.LeftHomologyData.ofZeros ((E.page r).sc pq)
      (E.page_d_eq_zero_of_single_row hRow r hr _ _)
      (E.page_d_eq_zero_of_single_row hRow r hr _ _)).homologyIso

/-- The canonical identification of a page term with its value on page two. -/
noncomputable def pageXIsoOfSingleRow (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (E.page r).X pq ≅ (E.page 2).X pq :=
  Int.leInduction (motive := fun r hr ↦ (E.page r (by lia)).X pq ≅ (E.page 2).X pq)
    (Iso.refl _) (fun s hs e ↦ E.pageSuccXIsoOfSingleRow hRow s hs pq ≪≫ e) r hr

end CategoryTheory.SpectralSequence
