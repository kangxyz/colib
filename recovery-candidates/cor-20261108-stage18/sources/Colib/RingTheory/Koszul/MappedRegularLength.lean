/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.RestrictionComparison
public import Colib.RingTheory.Koszul.Coefficients
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution

/-!
# Finite remaining Koszul homology after a nonflat change of coefficients

A sequence regular in the original ambient ring need not remain regular in a
closed coefficient quotient. Nevertheless its mapped ideal annihilates the
actual coefficient Koszul homology. The proof uses native Tor annihilation,
the regular Koszul resolution, and the actual restriction comparison.

If the target is Noetherian local and the mapped ideal is an ideal of definition,
finite coefficients therefore give finite homology length in every degree, including
zero modules. The native zero-inclusive support criterion supplies the conclusion.
No private native Koszul finite-length proof is copied, and no flatness of the
coefficient ring map is needed. The geometric application proves the ideal-of-
definition hypothesis from the original generic remaining intersection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace Koszul

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {r : ℕ}

/-- The mapped original regular-sequence ideal annihilates genuine coefficient
Koszul homology, even for a nonflat coefficient map. -/
theorem span_map_le_annihilator_seqComplexTensor_of_isRegular
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} R) (n : ℕ) :
    Ideal.span (Set.range (fun j => algebraMap A R (f j))) ≤
      Module.annihilator R
        ((seqComplexTensor (fun j => algebraMap A R (f j)) M).homology n) := by
  let N := (ModuleCat.restrictScalars (algebraMap A R)).obj M
  let I := Ideal.span (Set.range f)
  let e := torIsoHomologySeqComplexTensorOfIsRegular f hf I rfl N n ≪≫
    homologySeqComplexTensorRestrictScalarsIso f M n
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hj : f j ∈ Module.annihilator A (A ⧸ I) := by
    rw [Ideal.annihilator_quotient]
    exact Ideal.subset_span (Set.mem_range_self j)
  have hkill := mem_annihilator_of_moduleCat_iso e
    (mem_annihilator_tor_of_mem_annihilator (ModuleCat.of A (A ⧸ I)) N n hj)
  exact Module.mem_annihilator.mpr fun x => Module.mem_annihilator.mp hkill x

/-- Every actual coefficient Koszul homology has finite length when the mapped
original regular ideal has finite colength. No regularity is required in the target ring. -/
theorem length_seqComplexTensor_map_ne_top_of_isRegular [IsNoetherianRing R] [IsLocalRing R]
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j)))))
    (n : ℕ) :
    Module.length R
      ((seqComplexTensor (fun j => algebraMap A R (f j)) M).homology n) ≠ ⊤ := by
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_of_support_subset
  intro q hq
  have hann := Module.mem_support_iff_of_finite.mp hq
  have hle := (span_map_le_annihilator_seqComplexTensor_of_isRegular f hf M n).trans hann
  have hmax : IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
    rw [← hI]
    exact q.isPrime.radical_le_iff.mpr hle
  apply Set.mem_singleton_iff.mpr
  exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hmax)

end Koszul
