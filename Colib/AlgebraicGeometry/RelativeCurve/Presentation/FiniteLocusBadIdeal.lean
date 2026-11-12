/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryPrescribedScheme

/-! # A fixed original nonzero ideal controls the étale bad locus and prescribed scheme

The finite affine target open is constructed by the pinned native generic-fiber
finiteness theorem (Stacks Tag 02NW). No legacy envelope, chosen finite locus,
or normal-stalk compatibility is required. The complete original nonreduced J
is retained by the literal product I = J * K, chosen before any parameters.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry

/-- A nonempty affine open has a nonzero ideal defining its complete closed complement. -/
theorem vanishingIdeal_complement_ne_bot (B : Type u) [CommRing B]
    (U : (Spec (.of B)).Opens) (hU : (U : Set (Spec (.of B))).Nonempty) :
    PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of B)))ᶜ ≠ ⊥ := by
  intro he
  have hz := PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
    (U : Set (Spec (.of B)))ᶜ
  rw [he, PrimeSpectrum.zeroLocus_bot, U.isOpen.isClosed_compl.closure_eq] at hz
  obtain ⟨x, hx⟩ := hU
  have hxc : x ∈ (U : Set (Spec (.of B)))ᶜ := by
    rw [← hz]
    exact Set.mem_univ x
  exact hxc hx

/-- Before choosing any projection, the original étale map has a fixed nonzero
bad ideal. Its closed scheme contains the entire prescribed nonreduced quotient. -/
theorem exists_fixed_finite_locus_bad_ideal
    (B : Type u) [CommRing B] [IsDomain B] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ I : Ideal B, I ≠ ⊥ ∧ I ≤ J ∧
      ∃ U : (Spec (.of B)).Opens,
        (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ ∧
        IsFinite (p ∣_ U) := by
  have hη : genericPoint (Spec (.of B)) ∈ genericPoints (Spec (.of B)) := by
    rw [genericPoints_eq_singleton]
    rfl
  obtain ⟨V, hηV, hpV⟩ :=
    (finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict p
      (genericPoint (Spec (.of B))) hη).mp
      (p.finite_preimage_singleton (genericPoint (Spec (.of B))))
  have hV : (V.1 : Set (Spec (.of B))).Nonempty := ⟨_, hηV⟩
  let K := PrimeSpectrum.vanishingIdeal (V.1 : Set (Spec (.of B)))ᶜ
  have hK : K ≠ ⊥ := vanishingIdeal_complement_ne_bot B V.1 hV
  let I := J * K
  let U : (Spec (.of B)).Opens :=
    ⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩
  have hUV : U ≤ V.1 := by
    intro x hx
    by_contra hn
    apply hx
    apply PrimeSpectrum.zeroLocus_anti_mono_ideal Ideal.mul_le_right
    exact PrimeSpectrum.subset_zeroLocus_vanishingIdeal _ hn
  let : IsFinite (p ∣_ V.1) := hpV
  refine ⟨I, ?_, Ideal.mul_le_left, U, rfl,
    Scheme.RelativeCurve.finite_morphismRestrict_of_le p hUV⟩
  exact fun h => (Ideal.mul_eq_bot.mp h).elim hJ hK

end AlgebraicGeometry
