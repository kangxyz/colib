module

import Colib.FieldTheory.AdjoinRoot.Separable
import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePrime
import Colib.RingTheory.KTheory.MilnorK.Norm.MonicResiduePrime
import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeChosenPresentation
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.ComputeDegree
import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem.PowerSeriesRing

/-!
# A separable quadratic extension with inseparable residue

At the completed parameter `t = 0` over `𝔽₂(s)`, the monic polynomial
`Y² + tY - s` has nonzero derivative over the fraction field. Its residue
polynomial is the irreducible purely inseparable polynomial `Y² - s`.
-/

noncomputable section

open Polynomial IsLocalRing Module IntermediateField Stacks.Chow

namespace DVRInseparableResiduePositiveCharacteristic

private abbrev k := RatFunc (ZMod 2)
private abbrev R := PowerSeries k
private abbrev F := FractionRing R

private def p : R[X] :=
  X ^ 2 + C PowerSeries.X * X - C (PowerSeries.C (RatFunc.X : k))

private abbrev S := AdjoinRoot p
private abbrev E := AdjoinRoot (p.map (algebraMap R F))

private theorem p_monic : p.Monic := by
  unfold p
  monicity!

private theorem p_degree : p.natDegree = 2 := by
  unfold p
  compute_degree!

private theorem residue_identification (r : R) :
    PowerSeries.residueFieldOfPowerSeries (residue R r) = PowerSeries.constantCoeff r := by
  show (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
    (Ideal.quotEquivOfEq PowerSeries.ker_coeff_eq_max_ideal.symm
      (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

private theorem residue_parameter : residue R (PowerSeries.X : R) = 0 := by
  apply (PowerSeries.residueFieldOfPowerSeries (k := k)).injective
  rw [map_zero, residue_identification, PowerSeries.constantCoeff_X]

private theorem p_reduction :
    p.map (residue R) = X ^ 2 - C (residue R (PowerSeries.C (RatFunc.X : k))) := by
  simp only [p, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, residue_parameter, C_0, zero_mul, add_zero]

private theorem sq_ne_s (b : k) : b ^ 2 ≠ RatFunc.X := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa only [zero_pow (by decide : 2 ≠ 0)] using h.symm)
  have hd := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hb hb, RatFunc.intDegree_X] at hd
  omega

private theorem residue_sq_ne_s (b : ResidueField R) :
    b ^ 2 ≠ residue R (PowerSeries.C (RatFunc.X : k)) := by
  intro h
  have he := congrArg (PowerSeries.residueFieldOfPowerSeries (k := k)) h
  rw [map_pow, residue_identification, PowerSeries.constantCoeff_C] at he
  exact sq_ne_s _ he

private theorem residue_irreducible : Irreducible (p.map (residue R)) := by
  rw [p_reduction]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two residue_sq_ne_s

private theorem generic_irreducible : Irreducible (p.map (algebraMap R F)) :=
  AdjoinRoot.irreducible_map_algebraMap_of_irreducible_map_residue
    p_monic residue_irreducible

local instance : Fact (Irreducible (p.map (algebraMap R F))) := ⟨generic_irreducible⟩

local instance : IsDomain S :=
  AdjoinRoot.isDomain_of_irreducible_map_residue p_monic residue_irreducible

local instance : IsLocalRing S :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue p_monic residue_irreducible

private theorem p_degree_pos : 0 < p.natDegree := by
  rw [p_degree]
  decide

local instance : IsDiscreteValuationRing S :=
  AdjoinRoot.isDiscreteValuationRing p_monic residue_irreducible p_degree_pos

local instance : Module.Finite R S := p_monic.finite_adjoinRoot

local instance : IsLocalHom (algebraMap R S) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic p_monic

private theorem generic_separable : Algebra.IsSeparable F E := by
  apply AdjoinRoot.isSeparable_of_polynomial_separable
  apply (separable_iff_derivative_ne_zero generic_irreducible).2
  let f : ZMod 2 →+* F :=
    (algebraMap R F).comp (PowerSeries.C.comp (algebraMap (ZMod 2) k))
  have htwo : (2 : F) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg f (show (2 : ZMod 2) = 0 by decide)
  have htwoCast : ((2 : ℕ) : F) = 0 := by rw [Nat.cast_two, htwo]
  have hX : algebraMap R F PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr PowerSeries.X_ne_zero
  simpa only [p, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, derivative_sub, derivative_add,
    derivative_C, derivative_X_pow, derivative_C_mul_X, htwoCast, C_0, zero_mul, zero_add,
    sub_zero] using (Polynomial.C_ne_zero.mpr hX)

local instance : Algebra.IsSeparable F E := generic_separable

example : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S = 1 :=
  AdjoinRoot.ramificationIdx_eq_one p_monic residue_irreducible p_degree_pos

private theorem residue_degree : finrank (ResidueField R) (ResidueField S) = 2 :=
  (AdjoinRoot.finrank_residueField_eq_natDegree p_monic residue_irreducible
    p_degree_pos).trans p_degree

example : finrank (ResidueField R) (ResidueField S) = 2 := residue_degree

example : IsPurelyInseparable (ResidueField R) (ResidueField S) := by
  let a := residue S (AdjoinRoot.root p)
  have ha : aeval a (p.map (residue R)) = 0 := by
    have hcomp :
        (algebraMap (ResidueField R) (ResidueField S)).comp (residue R) =
          (residue S).comp (algebraMap R S) := RingHom.ext fun _ => rfl
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact AdjoinRoot.eval₂_residue_root_eq_zero (p := p)
  have hsq : a ^ 2 = algebraMap (ResidueField R) (ResidueField S)
      (residue R (PowerSeries.C (RatFunc.X : k))) := by
    simpa only [p_reduction, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using ha
  have hnot : a ∉ Set.range (algebraMap (ResidueField R) (ResidueField S)) := by
    rintro ⟨b, hb⟩
    apply residue_sq_ne_s b
    apply (algebraMap (ResidueField R) (ResidueField S)).injective
    rwa [map_pow, hb]
  have htop : (ResidueField R)⟮a⟯ = ⊤ :=
    adjoin_simple_eq_top_of_finrank_prime (residue_degree.symm ▸ Nat.prime_two) hnot
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  let e : k ≃+* ResidueField R := PowerSeries.residueFieldOfPowerSeries.symm
  let : CharP (ResidueField R) 2 := charP_of_injective_ringHom
    (f := e.toRingHom) e.injective 2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem
    (ResidueField R) (ResidueField S) 2 (x := a)).2 (by
      refine ⟨1, residue R (PowerSeries.C (RatFunc.X : k)), ?_⟩
      simpa only [pow_one] using hsq.symm)
  let : IsPurelyInseparable (ResidueField R) (⊤ : IntermediateField _ (ResidueField S)) :=
    htop ▸ h
  exact IntermediateField.topEquiv.isPurelyInseparable

private theorem generic_degree : finrank F E = 2 := by
  rw [AdjoinRoot.finrank_eq_natDegree (p_monic.map _), p_monic.natDegree_map, p_degree]

local instance : Algebra.IsQuadraticExtension F E where
  toFree := Module.Free.of_divisionRing F E
  finrank_eq_two' := generic_degree

local instance : IsAdicComplete (maximalIdeal R) R := by
  let : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  exact Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries k

local instance : Module.IsTorsionFree R S :=
  AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue p_monic residue_irreducible)
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp p_degree_pos))

local instance : Algebra S E :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot F (p := p) rfl).toAlgebra

local instance : IsScalarTower R S E := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change AdjoinRoot.of _ (algebraMap R F r) =
    Stacks.AdjoinRootFraction.toMapAdjoinRoot F rfl (AdjoinRoot.of p r)
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of F rfl r).symm

local instance : IsFractionRing S E :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot F rfl (RingEquiv.refl _)
    p_monic (by ext <;> rfl)

local instance : FiniteDimensional F E := (p_monic.map _).finite_adjoinRoot

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_complete_of_prime_galois
    R S F E (generic_degree.symm ▸ Nat.prime_two) n x

end DVRInseparableResiduePositiveCharacteristic
