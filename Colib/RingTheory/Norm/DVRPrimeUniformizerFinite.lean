/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.DVRPrimeUniformizer

import Colib.RingTheory.Charpoly.DVRResidueArbitrary

/-!
# Prime-degree uniformizer norm coefficients in every residue characteristic

In residue degree one, the multiplication characteristic polynomial determines
the exact normalized coefficient and its sign. The prime-degree dichotomy
combines this with the exponent-one coefficient.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u v w z

namespace IsDiscreteValuationRing

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]

/-- In residue degree one, the characteristic polynomial determines the exact
normalized coefficient of the integral norm of the upper uniformizer. -/
theorem exists_uniformizer_norm_coefficient_of_residue_finrank_one_any
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  have hepos : 0 < e := Nat.pos_of_ne_zero fun h =>
    hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π (by
      rw [he, h, pow_zero, mul_one]
      exact u.isUnit))
  have hϖres : residue S ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit
  let P := (Algebra.lmul R S ϖ).charpoly
  have hPmap : P.map (residue R) = X ^ e := by
    simpa only [hϖres, map_zero, LinearMap.charpoly_zero, hf, pow_one] using
      Algebra.residue_charpoly_lmul_eq_pow_arbitrary R S hπ hϖ u e he ϖ
  have hdegree : Module.finrank R S = e := by
    calc
      _ = P.natDegree := (LinearMap.charpoly_natDegree (Algebra.lmul R S ϖ)).symm
      _ = (P.map (residue R)).natDegree :=
        ((LinearMap.charpoly_monic (Algebra.lmul R S ϖ)).natDegree_map (residue R)).symm
      _ = e := by rw [hPmap, natDegree_X_pow]
  have hdiv : C π ∣ P - X ^ e := by
    apply (C_dvd_iff_dvd_coeff π _).mpr
    intro i
    apply Ideal.mem_span_singleton.mp
    rw [← (irreducible_iff_uniformizer π).mp hπ, ← residue_eq_zero_iff]
    have hzero : (P - X ^ e).map (residue R) = 0 := by
      rw [Polynomial.map_sub, hPmap, Polynomial.map_pow, Polynomial.map_X, sub_self]
    simpa only [coeff_map, coeff_zero] using
      congrArg (fun q : (ResidueField R)[X] => q.coeff i) hzero
  obtain ⟨g, hg⟩ := hdiv
  have hP : P = X ^ e + C π * g := by
    rw [add_comm, ← sub_eq_iff_eq_add]
    exact hg
  have hroot : aeval ϖ P = 0 := Algebra.aeval_self_charpoly_lmul ϖ
  rw [hP, map_add, map_pow, aeval_X, map_mul, aeval_C] at hroot
  have hsum : 1 + (u : S) * aeval ϖ g = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero e hϖ.ne_zero)
    rw [mul_zero]
    calc
      ϖ ^ e * (1 + (u : S) * aeval ϖ g) = ϖ ^ e + algebraMap R S π * aeval ϖ g := by
        rw [he]
        ring
      _ = 0 := hroot
  have heval : residue S (aeval ϖ g) =
      algebraMap (ResidueField R) (ResidueField S) (residue R (g.coeff 0)) := by
    rw [aeval_def, hom_eval₂, hϖres, eval₂_at_zero, RingHom.comp_apply,
      ResidueField.algebraMap_residue]
  have hproduct : residue S (u : S) *
      algebraMap (ResidueField R) (ResidueField S) (residue R (g.coeff 0)) = -1 := by
    apply eq_neg_of_add_eq_zero_right
    simpa only [map_add, map_one, map_mul, heval, map_zero] using congrArg (residue S) hsum
  let U := Algebra.norm (ResidueField R) (residue S (u : S))
  have hU : U ≠ 0 := ((u.isUnit.map (residue S)).map (Algebra.norm (ResidueField R))).ne_zero
  have hneg : Algebra.norm (ResidueField R) (-1 : ResidueField S) = -1 := by
    simpa only [map_neg, map_one, hf, pow_one] using
      (Algebra.norm_algebraMap (S := ResidueField S) (-1 : ResidueField R))
  have hnorm : U * residue R (g.coeff 0) = -1 := by
    simpa only [map_mul, Algebra.norm_algebraMap, hf, pow_one, hneg, U] using
      congrArg (Algebra.norm (ResidueField R)) hproduct
  have hres : residue R (g.coeff 0) = -U⁻¹ := by
    calc
      _ = U⁻¹ * (U * residue R (g.coeff 0)) := by rw [← mul_assoc, inv_mul_cancel₀ hU, one_mul]
      _ = _ := by rw [hnorm, mul_neg, mul_one]
  let b := (-1 : R) ^ e * g.coeff 0
  have hbRes : residue R b = (-1 : ResidueField R) ^ (e - 1) * U⁻¹ := by
    dsimp only [b]
    rw [map_mul, map_pow, map_neg, map_one, hres]
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ e from hepos), pow_succ]
    rw [mul_assoc, neg_one_mul, neg_neg]
  have hb : IsUnit b := by
    apply (residue_ne_zero_iff_isUnit b).mp
    rw [hbRes]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (inv_ne_zero hU)
  have hconst : P.coeff 0 = π * g.coeff 0 := by
    rw [hP, coeff_add, coeff_X_pow, coeff_C_mul]
    simp [Nat.ne_of_lt hepos]
  refine ⟨hb.unit, ?_, ?_⟩
  · rw [hb.unit_spec, Algebra.intNorm_eq_norm, Algebra.norm_apply,
      LinearMap.det_eq_sign_charpoly_coeff, hdegree]
    change (-1 : R) ^ e * P.coeff 0 = π * b
    rw [hconst]
    exact mul_left_comm _ _ _
  · simpa only [hb.unit_spec] using hbRes

include F E

omit [IsIntegralClosure S R E] in
/-- In prime fraction-field degree, the integral norm of the upper uniformizer
has the exact normalized coefficient in every residue characteristic. -/
theorem exists_uniformizer_norm_coefficient_of_prime_degree_any
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (hp : Nat.Prime (Module.finrank F E)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  rcases ramification_eq_one_or_residue_finrank_eq_one R S F E hπ hϖ u e he hp with he1 | hf1
  · subst e
    let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
    simpa only [Nat.sub_self, mul_zero, pow_zero, one_mul] using
      exists_uniformizer_norm_coefficient_of_exponent_one R S F E hπ hϖ u
        (by simpa only [pow_one] using he)
  · simpa only [hf1, pow_one, one_mul] using
      exists_uniformizer_norm_coefficient_of_residue_finrank_one_any R S hπ hϖ u e he hf1

end IsDiscreteValuationRing
