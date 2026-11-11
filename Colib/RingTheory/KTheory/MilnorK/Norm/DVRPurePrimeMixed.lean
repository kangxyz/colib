/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# The mixed norm-residue square in purely inseparable prime degree

The actual local degree formula separates ramification one from residue degree
one. The first case uses the existing mixed square. In the second, the integral
norm of an upper uniformizer is a base uniformizer and maps to its degree-th
power. This supplies the exact uniformizer coefficient one. Pure inseparability
also supplies the required sign, including characteristic two.

Only the native mixed span is treated here. No Henselianity, invertibility of
the ramification exponent, Milnor-group torsion-freeness, or all-symbol norm
square is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module IntermediateField

universe u v

namespace Stacks.Chow

private theorem purePrime_algebraMap_norm
    (F E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsPurelyInseparable F E] (x : E) :
    algebraMap F E (Algebra.norm F x) = x ^ finrank F E := by
  classical
  obtain ⟨r, hr⟩ :=
    IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
  have hd : (minpoly F x).natDegree = ringExpChar F ^ r := by
    have h := congrArg Polynomial.natDegree hr
    simpa only [Polynomial.natDegree_map, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one] using h
  have hs : ((minpoly F x).map (algebraMap F E)).Splits := by
    rw [hr]
    exact (Polynomial.Splits.X_sub_C x).pow _
  have ht : (minpoly F x).natDegree * finrank F⟮x⟯ E = finrank F E := by
    rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := F) x)]
    exact finrank_mul_finrank F F⟮x⟯ E
  rw [Algebra.norm_eq_prod_roots E hs, Polynomial.aroots_def, hr,
    Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.prod_nsmul,
    Multiset.prod_singleton, ← pow_mul, ← hd, ht]

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsPurelyInseparable F E]

omit [IsLocalHom (algebraMap R S)] in
private theorem purePrime_algebraMap_intNorm (a : S) :
    algebraMap R S (Algebra.intNorm R S a) = a ^ finrank F E := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  apply IsFractionRing.injective S E
  rw [← IsScalarTower.algebraMap_apply R S E,
    IsScalarTower.algebraMap_apply R F E,
    Algebra.algebraMap_intNorm (K := F) (L := E),
    map_pow]
  exact purePrime_algebraMap_norm F E (algebraMap S E a)

include F E in
private theorem purePrime_irreducible_intNorm_uniformizer
    {ρ : S} (hρ : Irreducible ρ)
    (hf : finrank (ResidueField R) (ResidueField S) = 1) :
    Irreducible (Algebra.intNorm R S ρ) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hn : Algebra.intNorm R S ρ ≠ 0 := by
    intro hz
    have h := congrArg (algebraMap R S) hz
    rw [purePrime_algebraMap_intNorm R S F E, map_zero] at h
    exact (pow_ne_zero _ hρ.ne_zero) h
  obtain ⟨m, b, hb⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hπ
  have heq :
      (Units.map (Algebra.norm F) (dvrFracUniformizer E hρ) : F) =
        algebraMap R F (b : R) * (algebraMap R F π) ^ (m : ℤ) := by
    change Algebra.norm F (algebraMap S E ρ) = _
    rw [← Algebra.algebraMap_intNorm (A := R) (B := S) (K := F) (L := E),
      hb, map_mul, map_pow, zpow_natCast]
  have hord := dvrFracOrd_eq_of_eq (u := b) (n := (m : ℤ)) hπ heq
  rw [dvrFracOrd_norm_uniformizer R S F E hπ hρ, hf] at hord
  have hm : m = 1 := by exact_mod_cast hord.symm
  rw [hb, hm, pow_one, mul_comm]
  exact (irreducible_mul_units b).mpr hπ

omit [Algebra R E] [IsScalarTower R F E] in
private theorem purePrime_residue_sign (hp : Nat.Prime (finrank F E)) :
    (-1 : ResidueField R) ^ (finrank F E - 1) = 1 := by
  let : ExpChar E (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow F E (ringExpChar F)
  have hneg : (-1 : R) ^ finrank F E = -1 := by
    apply IsFractionRing.injective R F
    apply (algebraMap F E).injective
    simpa only [map_pow, map_neg, map_one, hr] using
      (neg_one_pow_expChar_pow E (ringExpChar F) r)
  have hsign : (-1 : R) ^ (finrank F E - 1) = 1 := by
    apply mul_right_cancel₀ (neg_ne_zero.mpr (one_ne_zero : (1 : R) ≠ 0))
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne_zero),
      hneg, one_mul]
  have h := congrArg (residue R) hsign
  simpa only [map_pow, map_neg, map_one] using h

/-- In the residue-degree-one case the actual integral norm of an upper
uniformizer is a base uniformizer, with exact coefficient one and sign one. -/
theorem dvr_uniformizer_norm_of_isPurelyInseparable_of_prime
    (hp : Nat.Prime (finrank F E)) {ρ : S} (hρ : Irreducible ρ)
    (hf : finrank (ResidueField R) (ResidueField S) = 1) :
    Irreducible (Algebra.intNorm R S ρ) ∧
      algebraMap R S (Algebra.intNorm R S ρ) = ρ ^ finrank F E ∧
      (-1 : ResidueField R) ^ (finrank F E - 1) = 1 := by
  exact ⟨purePrime_irreducible_intNorm_uniformizer R S F E hρ hf,
    purePrime_algebraMap_intNorm R S F E ρ,
    purePrime_residue_sign (R := R) (F := F) (E := E) hp⟩

/-- The native norm-residue square on the existing mixed span for a finite
purely inseparable prime-degree extension of the fraction fields. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_isPurelyInseparable_of_prime
    (hp : Nat.Prime (finrank F E)) (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m
        (dvrMilnorTameSymbol' S E m x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hn : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hρ
  rcases IsDiscreteValuationRing.ramification_eq_one_or_residue_finrank_eq_one
      R S F E hπ hρ u e he hp with heone | hfone
  · subst e
    exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
      R S F E hπ hρ u (by simpa only [pow_one] using he) m x hx
  · obtain ⟨hν, hνmap, hsign⟩ :=
      dvr_uniformizer_norm_of_isPurelyInseparable_of_prime R S F E hp hρ hfone
    have he' : algebraMap R S (Algebra.intNorm R S ρ) =
        ((1 : Sˣ) : S) * ρ ^ finrank F E := by
      simpa only [Units.val_one, one_mul] using hνmap
    apply dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
      R S F E hν hρ 1 (finrank F E) he' 1
      (by simp only [hfone, pow_one, Units.val_one, mul_one])
      ?_ m x hx
    simp only [Units.val_one, map_one, hfone, one_mul, hsign, inv_one, mul_one]

end Stacks.Chow

end
