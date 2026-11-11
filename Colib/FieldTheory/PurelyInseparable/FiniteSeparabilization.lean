/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Finite purely inseparable base change for separability

Inside a perfect overfield, the image of a finite field extension becomes separable
over a finite purely inseparable extension of its base. The base change is generated
by the minimal polynomial coefficients of finitely many generators over the relative
perfect closure.
-/

public section

namespace IntermediateField

variable (K L D : Type*) [Field K] [Field L] [Field D]
  [Algebra K L] [Algebra K D] [Algebra L D] [IsScalarTower K L D]

/-- If a finite extension of `K` embeds in a perfect field `D`, there is a finite purely
inseparable intermediate field `B` of `D / K` over which every element of the image is
separable. -/
theorem exists_finiteDimensional_isPurelyInseparable_isSeparable
    [FiniteDimensional K L] [PerfectField D] :
    ∃ B : IntermediateField K D, FiniteDimensional K B ∧ IsPurelyInseparable K B ∧
      ∀ x : L, IsSeparable B (algebraMap L D x) := by
  classical
  obtain ⟨s, hs⟩ := fg_top K L
  let C := perfectClosure K D
  let p (x : L) : Polynomial C := minpoly C (algebraMap L D x)
  let coefficients := s.biUnion fun x ↦ (p x).coeffs.image (algebraMap C D)
  let B := adjoin K (coefficients : Set D)
  have hcoeff : ∀ z ∈ coefficients, z ∈ C := by
    intro z hz
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    exact c.property
  have hBC : B ≤ C := adjoin_le_iff.mpr hcoeff
  have hfinite : FiniteDimensional K B := finiteDimensional_adjoin fun z hz ↦ by
    let c : C := ⟨z, hcoeff z hz⟩
    exact (Algebra.IsIntegral.isIntegral c).map C.val
  refine ⟨B, hfinite, (le_perfectClosure_iff K D B).mp hBC, ?_⟩
  let j := (inclusion hBC).toRingHom
  have hsep : ∀ x ∈ s, IsSeparable B (algebraMap L D x) := by
    intro x hx
    have hlift : p x ∈ Polynomial.lifts j := by
      apply (Polynomial.lifts_iff_coeffs_subset_range (p x)).2
      intro c hc
      have hcD : (c : D) ∈ B := subset_adjoin K _ <|
        Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
      exact ⟨⟨c, hcD⟩, Subtype.ext rfl⟩
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (p x)).mp hlift
    have hxK : IsIntegral K (algebraMap L D x) :=
      (Algebra.IsIntegral.isIntegral x).map (IsScalarTower.toAlgHom K L D)
    have hxC : IsIntegral C (algebraMap L D x) := hxK.tower_top
    have hqsep : q.Separable := by
      apply (Polynomial.separable_map j).mp
      rw [hq]
      exact PerfectField.separable_of_irreducible (minpoly.irreducible hxC)
    have hqeval : Polynomial.aeval (algebraMap L D x) q = 0 := by
      rw [Polynomial.aeval_eq_aeval_map (φ := j) (RingHom.ext fun _ ↦ rfl), hq]
      exact minpoly.aeval C _
    exact hqsep.of_dvd (minpoly.dvd B _ hqeval)
  let E := ((separableClosure B D).restrictScalars K).comap (IsScalarTower.toAlgHom K L D)
  have hle : adjoin K (s : Set L) ≤ E :=
    adjoin_le_iff.mpr fun x hx ↦ mem_separableClosure_iff.mpr (hsep x hx)
  rw [hs] at hle
  intro x
  exact mem_separableClosure_iff.mp (hle (mem_top : x ∈ (⊤ : IntermediateField K L)))

end IntermediateField
