/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.ENat.BigOperators
public import StacksFrontier.Algebra.Homology.SpectralSequence.LengthDegeneration
import Mathlib.Tactic.Ring

/-!
# Alternating lengths of a convergent spectral sequence

Once a page has finite-length terms with finite support, its signed length sum equals
the signed length sum of the abutment. Both sums use the actual module structures.

The finite-support stabilization argument is adapted from
`CategoryTheory.SpectralSequence.exists_forall_hasEdgeMonoAt_hasEdgeEpiAt`
in Stacks `Algebra.Homology.SpectralSequence.EulerCharacteristic`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

universe u v

variable {R : Type u} [CommRing R] {r₀ : ℤ}

private theorem length_range_toCycles (C : ShortComplex (ModuleCat.{v} R)) :
    Module.length R (LinearMap.range C.toCycles.hom) =
      Module.length R (LinearMap.range C.f.hom) := by
  rw [← C.toCycles.hom.quotKerEquivRange.length_eq, ← C.f.hom.quotKerEquivRange.length_eq]
  have hk : LinearMap.ker C.toCycles.hom = LinearMap.ker C.f.hom := by
    ext x
    simp only [LinearMap.mem_ker]
    have hx : C.iCycles.hom (C.toCycles.hom x) = C.f.hom x :=
      congrArg (fun f : C.X₁ ⟶ C.X₂ => f.hom x) C.toCycles_i
    rw [← hx]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      exact (ModuleCat.mono_iff_injective C.iCycles).1 inferInstance
        (h.trans (map_zero C.iCycles.hom).symm)
  rw [hk]

private theorem finsum_euler_page_succ (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset (ℤ × ℤ))
    (hf : ∀ pq, Module.length R ((E.page r hr).X pq) ≠ ⊤)
    (hz : ∀ pq ∉ s, IsZero ((E.page r hr).X pq)) :
    (∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
      ((Module.length R ((E.page r hr).X pq)).toNat : ℤ)) =
    ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
      ((Module.length R ((E.page (r + 1) (by omega)).X pq)).toNat : ℤ) := by
  classical
  let C := E.page r hr
  let σ : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.addRight (r, 1 - r)
  let ε : ℤ × ℤ → ℤ := fun pq => (pq.1 + pq.2).negOnePow
  let b : ℤ × ℤ → ℤ := fun pq => ε pq * (Module.length R (C.d pq (σ pq)).hom.range).toNat
  let h : ℤ × ℤ → ℤ := fun pq => ε pq * (Module.length R (C.homology pq)).toNat
  have hσ (pq : ℤ × ℤ) : (ComplexShape.up' (r, 1 - r)).Rel pq (σ pq) := rfl
  have hs (pq : ℤ × ℤ) : ε (σ pq) = -ε pq := by
    change ((pq.1 + r + (pq.2 + (1 - r))).negOnePow : ℤ) = _
    rw [show pq.1 + r + (pq.2 + (1 - r)) = pq.1 + pq.2 + 1 by omega,
      Int.negOnePow_succ, Units.val_neg]
  have hb : (Function.support b).Finite := s.finite_toSet.subset fun pq hpq => by
    by_contra hn
    have hdz : C.d pq (σ pq) = 0 := (hz pq hn).eq_of_src _ _
    exact hpq (by simp [b, ShortComplex.moduleCat_length_range_eq_zero _ hdz])
  have hh : (Function.support h).Finite := s.finite_toSet.subset fun pq hpq => by
    by_contra hn
    have hlen := (ModuleCat.length_eq_zero_iff_isZero (C.homology pq)).2
      ((C.sc pq).isZero_homology_of_isZero_X₂ (hz pq hn))
    exact hpq (by simp [h, hlen])
  have hEq (pq : ℤ × ℤ) : ε pq * (Module.length R (C.X pq)).toNat =
      h pq + b pq - b (σ.symm pq) := by
    have hc := (C.sc pq).moduleCat_length_X₂_eq
    rw [length_range_toCycles] at hc
    change Module.length R (C.X pq) = Module.length R (C.d _ pq).hom.range +
      Module.length R (C.homology pq) + Module.length R (C.d pq _).hom.range at hc
    have hfin := hf pq
    change Module.length R (C.X pq) ≠ ⊤ at hfin
    rw [hc, ne_eq, ENat.add_eq_top, ENat.add_eq_top, not_or, not_or] at hfin
    have hp : (ComplexShape.up' (r, 1 - r)).prev pq = σ.symm pq :=
      (ComplexShape.up' (r, 1 - r)).prev_eq' (by simpa using hσ (σ.symm pq))
    have hn : (ComplexShape.up' (r, 1 - r)).next pq = σ pq :=
      (ComplexShape.up' (r, 1 - r)).next_eq' (hσ pq)
    have he : ε pq = -ε (σ.symm pq) := by simpa using hs (σ.symm pq)
    dsimp only [h, b]
    rw [hc, ENat.toNat_add (by simp [hfin]) hfin.2, ENat.toNat_add hfin.1.1 hfin.1.2,
      Nat.cast_add, Nat.cast_add, hp, hn, σ.apply_symm_apply, he]
    ring
  change (∑ᶠ pq, ε pq * (Module.length R (C.X pq)).toNat) = _
  simp_rw [hEq]
  have hb' : (Function.support (fun pq => b (σ.symm pq))).Finite :=
    hb.preimage σ.symm.injective.injOn
  have hhb : (Function.support (fun pq => h pq + b pq)).Finite :=
    (hh.union hb).subset (Function.support_add _ _)
  rw [finsum_sub_distrib hhb hb', finsum_add_distrib hh hb, finsum_comp_equiv σ.symm,
    add_sub_cancel_right]
  refine finsum_congr fun pq => ?_
  dsimp only [h]
  rw [(E.iso r (r + 1) pq rfl hr).toLinearEquiv.length_eq]

-- The coordinate change of a differential eventually exceeds the spread of finite support.
private theorem exists_stablePage (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset (ℤ × ℤ))
    (hs : ∀ t (ht : r ≤ t), ∀ pq ∉ s, IsZero ((E.page t (hr.trans ht)).X pq)) :
    ∃ t : ℤ, r ≤ t ∧ ∀ pq, t ∈ E.hasEdgeMonoSet pq ∧ t ∈ E.hasEdgeEpiSet pq := by
  let B : ℤ := ∑ pq ∈ s, |pq.1|
  have hB (pq : ℤ × ℤ) (h : pq ∈ s) : -B ≤ pq.1 ∧ pq.1 ≤ B :=
    abs_le.1 (Finset.single_le_sum (f := fun pq : ℤ × ℤ => |pq.1|) (fun _ _ => abs_nonneg _) h)
  have hd (t : ℤ) (ht : max r (2 * B + 1) ≤ t) (pq pq' : ℤ × ℤ) :
      (E.page t (by omega)).d pq pq' = 0 := by
    by_cases hrel : (ComplexShape.up' (t, 1 - t)).Rel pq pq'
    · by_cases h₁ : pq ∈ s
      · by_cases h₂ : pq' ∈ s
        · exfalso
          have e := congrArg _root_.Prod.fst hrel
          simp only [_root_.Prod.fst_add] at e
          have := hB pq h₁
          have := hB pq' h₂
          omega
        · exact (hs t (by omega) pq' h₂).eq_of_tgt _ _
      · exact (hs t (by omega) pq h₁).eq_of_src _ _
    · exact (E.page t (by omega)).shape _ _ hrel
  refine ⟨max r (2 * B + 1), le_max_left _ _, fun pq => ⟨⟨by omega, fun t ht => ?_⟩,
    ⟨by omega, fun t ht => ?_⟩⟩⟩
  · exact ⟨by omega, fun pq' => hd t ht pq' pq⟩
  · exact ⟨by omega, fun pq' => hd t ht pq pq'⟩

/-- The alternating sum of finite module lengths on a finitely supported page equals the
alternating sum of module lengths in the abutment. -/
theorem AbutsTo.finsum_length_eq {E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀}
    {H : ℤ → ModuleCat.{v} R} (hE : E.AbutsTo H) (r : ℤ) (hr : r₀ ≤ r)
    (hf : ∀ pq, Module.length R ((E.page r hr).X pq) ≠ ⊤)
    (hsupp : {pq | ¬ IsZero ((E.page r hr).X pq)}.Finite) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * ((Module.length R (H n)).toNat : ℤ)) =
      ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
        ((Module.length R ((E.page r hr).X pq)).toNat : ℤ) := by
  classical
  let s := hsupp.toFinset
  have hpage (t : ℤ) (ht : r ≤ t) (pq : ℤ × ℤ) :
      Module.length R ((E.page t (hr.trans ht)).X pq) ≤ Module.length R ((E.page r hr).X pq) :=
    E.length_page_le pq r t ht hr
  have hzero (t : ℤ) (ht : r ≤ t) (pq : ℤ × ℤ) (hpq : pq ∉ s) :
      IsZero ((E.page t (hr.trans ht)).X pq) := by
    have hz : IsZero ((E.page r hr).X pq) := by simpa [s] using hpq
    refine (ModuleCat.length_eq_zero_iff_isZero _).1 (le_zero_iff.1 ?_)
    exact (hpage t ht pq).trans ((ModuleCat.length_eq_zero_iff_isZero _).2 hz).le
  have heuler (t : ℤ) (ht : r ≤ t) :
      (∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
        ((Module.length R ((E.page r hr).X pq)).toNat : ℤ)) =
      ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
        ((Module.length R ((E.page t (hr.trans ht)).X pq)).toNat : ℤ) := by
    induction t, ht using Int.leInduction with
    | base => rfl
    | succ t ht ih =>
      exact ih.trans (finsum_euler_page_succ E t (hr.trans ht) s
        (fun pq => ne_top_of_le_ne_top (hf pq) (hpage t ht pq)) (hzero t ht))
  obtain ⟨t, ht, hstable⟩ := exists_stablePage E r hr s hzero
  have eInf (pq : ℤ × ℤ) : Nonempty (E.pageInfinity pq ≅ (E.page t (hr.trans ht)).X pq) := by
    have : E.HasPageInfinityAt pq := ⟨⟨t, (hstable pq).1⟩, ⟨t, (hstable pq).2⟩⟩
    have : E.HasEdgeMonoAtFrom pq t := ⟨E.rToMin_LE pq t (hstable pq).1⟩
    have : E.HasEdgeEpiAtFrom pq t := ⟨E.rFromMin_LE pq t (hstable pq).2⟩
    exact ⟨E.pageInfinityIso pq t⟩
  let l : ℤ × ℤ → ℕ∞ := fun pq => Module.length R ((E.page t (hr.trans ht)).X pq)
  have hl (pq : ℤ × ℤ) : l pq ≠ ⊤ := ne_top_of_le_ne_top (hf pq) (hpage t ht pq)
  have hlz (pq : ℤ × ℤ) (hpq : pq ∉ s) : l pq = 0 :=
    (ModuleCat.length_eq_zero_iff_isZero _).2 (hzero t ht pq hpq)
  have hH (n : ℤ) : (Module.length R (H n)).toNat = ∑ᶠ p : ℤ, (l (p, n - p)).toNat := by
    have hz (p : ℤ) (hp : p ∉ s.image _root_.Prod.fst) : (p, n - p) ∉ s :=
      fun h => hp (Finset.mem_image_of_mem _ h)
    rw [length_abutment_eq_sum_pageInfinity hE n (s.image _root_.Prod.fst) (fun p hp =>
      (hzero t ht (p, n - p) (hz p hp)).of_iso (eInf _).some)]
    simp_rw [(eInf _).some.toLinearEquiv.length_eq]
    change (∑ p ∈ s.image _root_.Prod.fst, l (p, n - p)).toNat = _
    rw [ENat.toNat_sum (fun p _ => hl (p, n - p)), finsum_eq_sum_of_support_subset]
    exact fun p hp => by_contra fun hn => hp (by simp [hlz _ (hz p hn)])
  let φ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun np => (np.2, np.1 - np.2)
      invFun := fun pq => (pq.1 + pq.2, pq.1)
      left_inv := fun np => by ext <;> simp
      right_inv := fun pq => by ext <;> simp }
  let a : ℤ × ℤ → ℤ := fun pq => ((pq.1 + pq.2).negOnePow : ℤ) * (l pq).toNat
  have ha : (Function.support a).Finite := s.finite_toSet.subset fun pq hp =>
    by_contra fun hn => hp (by simp [a, hlz pq hn])
  have hfiber (n : ℤ) : (Function.support fun p : ℤ => (l (p, n - p)).toNat).Finite :=
    (s.image _root_.Prod.fst).finite_toSet.subset fun p hp => by
      by_contra hn
      exact hp (by simp [hlz (p, n - p) (fun h => hn (Finset.mem_image_of_mem _ h))])
  calc
    _ = ∑ᶠ n : ℤ, ∑ᶠ p : ℤ, a (φ (n, p)) := by
      refine finsum_congr fun n => ?_
      have hcast : ((∑ᶠ p : ℤ, (l (p, n - p)).toNat : ℕ) : ℤ) =
          ∑ᶠ p : ℤ, ((l (p, n - p)).toNat : ℤ) :=
        (Nat.castAddMonoidHom ℤ).map_finsum (hfiber n)
      rw [hH n, hcast, mul_finsum]
      refine finsum_congr fun p => ?_
      simp [a, φ]
    _ = ∑ᶠ np : ℤ × ℤ, a (φ np) := (finsum_curry _ (ha.preimage φ.injective.injOn)).symm
    _ = ∑ᶠ pq : ℤ × ℤ, a pq := finsum_comp_equiv φ
    _ = _ := (heuler t ht).symm

/-- Finite lengths and finite support on a page give finite lengths and finite support on
the abutment. -/
theorem AbutsTo.finiteLength_and_support {E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀}
    {H : ℤ → ModuleCat.{v} R} (hE : E.AbutsTo H) (r : ℤ) (hr : r₀ ≤ r)
    (hf : ∀ pq, Module.length R ((E.page r hr).X pq) ≠ ⊤)
    (hsupp : {pq | ¬ IsZero ((E.page r hr).X pq)}.Finite) :
    (∀ n, IsFiniteLength R (H n)) ∧ {n | ¬ IsZero (H n)}.Finite := by
  classical
  let s := hsupp.toFinset
  have hInf (pq : ℤ × ℤ) : Module.length R (E.pageInfinity pq) ≤
      Module.length R ((E.page r hr).X pq) := by
    have : E.HasPageInfinityAt pq := hE.1 pq.1 pq.2
    exact E.length_pageInfinity_le pq r hr
  have hzero (pq : ℤ × ℤ) (hpq : pq ∉ s) : IsZero (E.pageInfinity pq) := by
    have h := (ModuleCat.length_eq_zero_iff_isZero ((E.page r hr).X pq)).2
      (by simpa [s] using hpq)
    exact (ModuleCat.length_eq_zero_iff_isZero _).1 (le_zero_iff.1 ((hInf pq).trans h.le))
  have hH (n : ℤ) : Module.length R (H n) =
      ∑ p ∈ s.image _root_.Prod.fst, Module.length R (E.pageInfinity (p, n - p)) :=
    length_abutment_eq_sum_pageInfinity hE n (s.image _root_.Prod.fst) fun p hp =>
      hzero (p, n - p) fun h => hp (Finset.mem_image_of_mem _ h)
  constructor
  · intro n
    apply Module.length_ne_top_iff.mp
    rw [hH n, ENat.sum_ne_top]
    exact fun p _ => ne_top_of_le_ne_top (hf (p, n - p)) (hInf (p, n - p))
  · refine (s.finite_toSet.image fun pq => pq.1 + pq.2).subset fun n hn => ?_
    by_contra hn'
    apply hn
    apply (ModuleCat.length_eq_zero_iff_isZero _).1
    rw [hH n]
    apply Finset.sum_eq_zero
    intro p _
    refine (ModuleCat.length_eq_zero_iff_isZero _).2 (hzero (p, n - p) fun hp => hn' ?_)
    exact ⟨(p, n - p), hp, by simp⟩

end CategoryTheory.SpectralSequence
