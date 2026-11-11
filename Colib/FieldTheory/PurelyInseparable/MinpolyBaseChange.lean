/-
Copyright (c) 2023 Jz Pan and 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan, kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Minimal polynomials after purely inseparable base change

In a supplied field tower `K → K' → D`, with `K' / K` purely inseparable,
the coefficient image of the minimal polynomial of an integral element `a : D`
is a power of its minimal polynomial over `K'`. Its exponent is the literal
polynomial multiplicity. If `a` is separable over `K'`, this exponent is the
inseparable degree of the original simple extension `K(a) / K`.

The ambient field need not be finite over either base, and the three fields may
have independent universes. Thus `a` may be the image of an element of another
field under an actual embedding into `D`.

The private factor-removal lemma adapts Jz Pan's Lean proof of Mathlib's
`Polynomial.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one`, in
`Mathlib/FieldTheory/SeparableDegree.lean:592-610` at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The degree comparisons use the
existing purely inseparable adjoin and field-degree tower results.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u v w

private theorem Polynomial.eq_pow_multiplicity_of_natSepDegree_eq
    {F : Type*} [Field F] {f q : F[X]} (hf : f.Monic) (hq : q.Monic)
    (hirr : Irreducible q) (hdvd : q ∣ f) (hdeg : f.natSepDegree = q.natSepDegree) :
    f = q ^ multiplicity q f := by
  have hfinite := finiteMultiplicity_of_degree_pos_of_monic
    (degree_pos_of_irreducible hirr) hq hf.ne_zero
  have hmult : multiplicity q f ≠ 0 := (multiplicity_pos_of_dvd hdvd hfinite).ne'
  obtain ⟨c, hfactor, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  rw [hfactor, natSepDegree_mul_of_isCoprime _ c <| IsCoprime.pow_left <|
    (hirr.isCoprime_or_dvd c).resolve_right hnot,
    natSepDegree_pow_of_ne_zero _ hmult, add_eq_left, natSepDegree_eq_zero_iff] at hdeg
  have hc : c = 1 :=
    eq_one_of_monic_natDegree_zero ((hq.pow _).of_mul_monic_left (hfactor ▸ hf)) hdeg
  simpa only [hc, mul_one] using hfactor

namespace minpoly

variable {K : Type u} (K' : Type v) {D : Type w}
  [Field K] [Field K'] [Field D]
  [Algebra K K'] [Algebra K D] [Algebra K' D] [IsScalarTower K K' D]
  [IsPurelyInseparable K K']

/-- Purely inseparable extension of the coefficient field preserves the separable
degree of the minimal polynomial of an integral ambient element. -/
theorem natSepDegree_eq_of_isPurelyInseparable (a : D) (ha : IsIntegral K a) :
    (minpoly K' a).natSepDegree = (minpoly K a).natSepDegree := by
  have ha' : IsIntegral K' a := ha.tower_top
  let : Algebra.IsAlgebraic K K⟮a⟯ := isAlgebraic_adjoin_simple ha
  let : Algebra.IsAlgebraic K' K'⟮a⟯ := isAlgebraic_adjoin_simple ha'
  have h := congrArg Cardinal.toNat
    (sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
      (F := K) K' ({a} : Set D))
  rw [← Field.finSepDegree_eq K' K'⟮a⟯, ← Field.finSepDegree_eq K K⟮a⟯,
    finSepDegree_adjoin_simple_eq_natSepDegree K' D ha'.isAlgebraic,
    finSepDegree_adjoin_simple_eq_natSepDegree K D ha.isAlgebraic] at h
  exact h

/-- The coefficient image of an integral element's minimal polynomial is the
power of its new minimal polynomial with its exact polynomial multiplicity. -/
theorem map_eq_pow_multiplicity_of_isPurelyInseparable (a : D) (ha : IsIntegral K a) :
    (minpoly K a).map (algebraMap K K') =
      (minpoly K' a) ^
        multiplicity (minpoly K' a) ((minpoly K a).map (algebraMap K K')) := by
  have ha' : IsIntegral K' a := ha.tower_top
  apply Polynomial.eq_pow_multiplicity_of_natSepDegree_eq
    ((minpoly.monic ha).map _) (minpoly.monic ha') (minpoly.irreducible ha')
    (minpoly.dvd_map_of_isScalarTower K K' a)
  rw [Polynomial.natSepDegree_map]
  exact (natSepDegree_eq_of_isPurelyInseparable K' a ha).symm

/-- When the new minimal polynomial is separable, its multiplicity in the
coefficient image equals the inseparable degree of the original simple field. -/
theorem multiplicity_map_eq_finInsepDegree_of_isSeparable_of_isPurelyInseparable
    (a : D) (ha : IsIntegral K a) (hsep : IsSeparable K' a) :
    multiplicity (minpoly K' a) ((minpoly K a).map (algebraMap K K')) =
      Field.finInsepDegree K K⟮a⟯ := by
  have ha' : IsIntegral K' a := ha.tower_top
  have hsepdegree : Field.finSepDegree K K⟮a⟯ = (minpoly K' a).natDegree := by
    rw [finSepDegree_adjoin_simple_eq_natSepDegree K D ha.isAlgebraic,
      ← natSepDegree_eq_of_isPurelyInseparable K' a ha]
    exact hsep.natSepDegree_eq_natDegree
  have hproduct := Field.finSepDegree_mul_finInsepDegree K K⟮a⟯
  rw [hsepdegree, IntermediateField.adjoin.finrank ha] at hproduct
  have hdegree := congrArg Polynomial.natDegree
    (map_eq_pow_multiplicity_of_isPurelyInseparable K' a ha)
  simp only [Polynomial.natDegree_map, Polynomial.natDegree_pow] at hdegree
  apply mul_right_cancel₀ (minpoly.irreducible ha').natDegree_pos.ne'
  exact hdegree.symm.trans (by simpa only [mul_comm] using hproduct.symm)

/-- After a purely inseparable base change that makes the ambient element
separable, its original minimal polynomial is the power of its new one by the
original simple extension's inseparable degree. -/
theorem map_eq_pow_finInsepDegree_of_isSeparable_of_isPurelyInseparable
    (a : D) (ha : IsIntegral K a) (hsep : IsSeparable K' a) :
    (minpoly K a).map (algebraMap K K') =
      (minpoly K' a) ^ Field.finInsepDegree K K⟮a⟯ := by
  rw [map_eq_pow_multiplicity_of_isPurelyInseparable K' a ha,
    multiplicity_map_eq_finInsepDegree_of_isSeparable_of_isPurelyInseparable K' a ha hsep]

end minpoly

end
