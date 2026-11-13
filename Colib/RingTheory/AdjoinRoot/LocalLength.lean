/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Length of a native polynomial branch

The actual localization of the whole root algebra at the factor-map kernel
has the length of its defining equation in the original polynomial DVR.
The maximal ideal power records the full multiplicity of the factor.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

namespace AdjoinRoot

variable {k : Type u} [Field k]

private theorem selfLength_eq_coheight_bot (R : Type u) [CommRing R] :
    Module.length R R = Order.coheight (⊥ : Ideal R) := by
  rw [← (AlgEquiv.quotientBot R R).toLinearEquiv.length_eq, Module.length_quotient]

/-- The native localization at a factor-map kernel has the full factor multiplicity. -/
theorem branch_localLength (f : k[X]) (hf : f ≠ 0)
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree k e // poly r.2 ∣ f}) :
    let A := Localization.AtPrime (nativeFactorMaximal f r).asIdeal
    Module.length A A = (multiplicity (poly r.1.2) f : ℕ∞) := by
  let q := poly r.1.2
  let m := nativeFactorMaximal f r
  let P := m.asIdeal.comap (AdjoinRoot.mk f)
  let D := Localization.AtPrime P
  let A := Localization.AtPrime m.asIdeal
  let g : D →+* A := Localization.localRingHom P m.asIdeal (AdjoinRoot.mk f) rfl
  have hP : P = Ideal.span {q} := nativeFactorMaximal_comap_mk f r
  have hq : Irreducible q := irreducible r.1.2
  have hP0 : P ≠ ⊥ := by
    intro h
    exact hq.ne_zero (Ideal.span_singleton_eq_bot.mp (hP.symm.trans h))
  let : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hP0 D
  have hmk : Function.Surjective (AdjoinRoot.mk f) := AdjoinRoot.mk_surjective
  have hsub : Submonoid.map (AdjoinRoot.mk f) P.primeCompl = m.asIdeal.primeCompl := by
    change Submonoid.map (AdjoinRoot.mk f) (m.asIdeal.primeCompl.comap (AdjoinRoot.mk f)) =
      m.asIdeal.primeCompl
    exact Submonoid.map_comap_eq_of_surjective hmk m.asIdeal.primeCompl
  have hker : RingHom.ker g = (Ideal.span {f}).map (algebraMap k[X] D) := by
    have h := IsLocalization.ker_map (S := D) A (AdjoinRoot.mk f) hsub
    change RingHom.ker g = (RingHom.ker (AdjoinRoot.mk f)).map (algebraMap k[X] D) at h
    change RingHom.ker g =
      (RingHom.ker (Ideal.Quotient.mk (Ideal.span {f}))).map (algebraMap k[X] D) at h
    rwa [Ideal.mk_ker] at h
  obtain ⟨c, hc, hqc⟩ :=
    (FiniteMultiplicity.of_not_isUnit hq.not_isUnit hf).exists_eq_pow_mul_and_not_dvd
  have hcu : IsUnit (algebraMap k[X] D c) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff D P c).mpr (by
      change c ∉ P
      rw [hP, Ideal.mem_span_singleton]
      exact hqc)
  have hgen : Ideal.span {algebraMap k[X] D q} = IsLocalRing.maximalIdeal D := by
    calc
      _ = (Ideal.span {q}).map (algebraMap k[X] D) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = _ := (congrArg (fun I : Ideal k[X] => I.map (algebraMap k[X] D)) hP.symm).trans
        (Localization.AtPrime.map_eq_maximalIdeal (I := P))
  have hmap : algebraMap k[X] D f =
      (algebraMap k[X] D q) ^ multiplicity q f * algebraMap k[X] D c := by
    exact (congrArg (algebraMap k[X] D) hc).trans (by rw [map_mul, map_pow])
  have hpow : RingHom.ker g = IsLocalRing.maximalIdeal D ^ multiplicity q f := by
    rw [hker, Ideal.map_span, Set.image_singleton, hmap,
      Ideal.span_singleton_mul_right_unit hcu, ← Ideal.span_singleton_pow, hgen]
  have hsurj : Function.Surjective g :=
    RingHom.surjective_localRingHom_of_surjective (AdjoinRoot.mk f) hmk m.asIdeal
  change Module.length A A = (multiplicity q f : ℕ∞)
  rw [selfLength_eq_coheight_bot]
  calc
    _ = Order.coheight (RingHom.ker g) :=
      (Ideal.coheight_comap_of_surjective g hsurj (⊥ : Ideal A)).symm
    _ = _ := by
      rw [hpow]
      exact IsDiscreteValuationRing.coheight_pow_maximalIdeal D (multiplicity q f)

end AdjoinRoot
