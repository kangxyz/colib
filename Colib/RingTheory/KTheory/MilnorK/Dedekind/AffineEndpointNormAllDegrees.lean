/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero

/-!
# Actual weighted endpoint norm equality, including degree zero

Adapted from Aglib `Dedekind/AffineEndpointNormAllDegrees.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 32–90.
The zero case uses the actual native degree-zero comparison with integers and
its field-map naturality. All branches and their actual orders remain in the
sum. No positive-degree hypothesis, endpoint boundary, or assumed square is added.
-/

@[expose] public noncomputable section
namespace Stacks.Chow.DedekindResidue

open Polynomial PolynomialResidue IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

omit [CharZero k] in
/-- Constant restriction is surjective on the actual native K₀, through its integer comparison. -/
theorem constant_restriction_zero_surjective :
    Function.Surjective (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) 0) := by
  intro x
  refine ⟨(milnorKTheoryZeroAddEquiv k).symm (milnorKTheoryZeroAddEquiv (RatFunc k) x), ?_⟩
  apply (milnorKTheoryZeroAddEquiv (RatFunc k)).injective
  rw [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
    milnorKTheoryZeroAddEquiv_milnorKTransport]
  exact (milnorKTheoryZeroAddEquiv k).apply_symm_apply _

/-- Global ring-unit symbols have constant norms in every degree, including the empty tuple. -/
theorem norm_ring_unit_symbol_mem_constant_range_all (n : ℕ) (u : Fin n → Sˣ) :
    milnorKNorm (RatFunc k) E n
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u)) ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n) := by
  cases n with
  | zero => exact constant_restriction_zero_surjective k _
  | succ n => exact norm_ring_unit_symbol_mem_constant_range k S E n u

/-- Equality of literal norm specializations at any two endpoints, in every degree. -/
theorem linearSpecialization_norm_ring_unit_symbol_eq_all (a b : k) (n : ℕ)
    (u : Fin n → Sˣ) :
    linearSpecialization a n (milnorKNorm (RatFunc k) E n
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization b n (milnorKNorm (RatFunc k) E n
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_eq_of_mem_constant_range a b n _
    (norm_ring_unit_symbol_mem_constant_range_all k S E n u)

/-- The actual weighted branch sum equals actual norm specialization even in degree zero. -/
theorem endpointWeightedResidueSum_eq_specialization_all (a : k) (n : ℕ)
    (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u =
      linearSpecialization a n (milnorKNorm (RatFunc k) E n
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) := by
  rw [← linearResidue_norm_unit_symbol_last, ← milnorKMulSymbol_tupleSymbol]
  unfold endpointParameter
  rw [milnorKNorm_mulSymbol]
  exact linearResidue_mulSymbol_eq_specialization a n _
    (norm_ring_unit_symbol_mem_constant_range_all k S E n u)

/-- Any two actual endpoint sums agree in every degree, with all branches and integer weights. -/
theorem endpointWeightedResidueSum_eq_all (a b : k) (n : ℕ) (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u = endpointWeightedResidueSum k S E b n u := by
  rw [endpointWeightedResidueSum_eq_specialization_all,
    endpointWeightedResidueSum_eq_specialization_all]
  exact linearSpecialization_norm_ring_unit_symbol_eq_all k S E a b n u

end Stacks.Chow.DedekindResidue
