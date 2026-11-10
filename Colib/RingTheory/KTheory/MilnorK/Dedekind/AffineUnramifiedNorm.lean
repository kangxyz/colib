/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueDirectSum
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.PolynomialResidue
public import Colib.RingTheory.KTheory.MilnorK.RationalFunctionExactness

/-!
# Actual norms of unramified affine classes are constant

Adapted from Aglib `Dedekind/AffineUnramifiedNorm.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 29–68.
The original all-branch square and native Bass–Tate exactness are used, on the
original field and localizations. No norm or residue compatibility is assumed.
-/

@[expose] public noncomputable section
namespace Stacks.Chow.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The native norm of an everywhere unramified affine class is constant. -/
theorem norm_mem_constant_range_of_totalResidue_zero (n : ℕ)
    (x : MilnorKTheory E (n + 1)) (hx : totalResidue S E n x = 0) :
    milnorKNorm (RatFunc k) E (n + 1) x ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) (n + 1)) := by
  classical
  let : ∀ p : HeightOneSpectrum k[X],
      CharZero (ResidueField (Localization.AtPrime p.asIdeal)) := fun p =>
    charZero_of_injective_algebraMap
      (algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))).injective
  have hz : totalResidue k[X] (RatFunc k) n
      (milnorKNorm (RatFunc k) E (n + 1) x) = 0 := by
    rw [totalResidue_milnorKNorm k[X] S (RatFunc k) E, hx, map_zero]
  have hnative : milnorKTotalResidue k n (milnorKNorm (RatFunc k) E (n + 1) x) = 0 := by
    apply DFinsupp.ext
    intro p
    rw [← PolynomialDedekindResidue.totalResidue_point, hz]
    simp
  have hr : milnorKNorm (RatFunc k) E (n + 1) x ∈
      (constantInclusion (k := k) (n + 1)).range := by
    rw [← ker_milnorKTotalResidue]
    exact hnative
  have hc : constantsHom k = (RatFunc.C : k →+* RatFunc k) := by
    ext c
    exact RatFunc.algebraMap_C c
  rw [milnorKTheoryMap_eq_transport]
  change milnorKNorm (RatFunc k) E (n + 1) x ∈
    (milnorKTransport (RatFunc.C : k →+* RatFunc k) (n + 1)).range
  simpa only [constantInclusion, hc] using hr

/-- Every tuple of global ring units has zero residue at every original point. -/
theorem totalResidue_ring_units (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    totalResidue S E n
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) = 0 := by
  apply (totalResidue_eq_zero_iff S E n _).mpr
  intro q
  apply dvrMilnorTameSymbol'_eq_zero_of_milnorKSymbolProd n
    (List.ofFn (Units.map (algebraMap S E).toMonoidHom ∘ a)) rfl
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  refine ⟨Units.map (algebraMap S (Localization.AtPrime q.asIdeal)).toMonoidHom (a i), ?_⟩
  exact (IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E (a i)).symm

/-- Global unit symbols have constant actual norms, without a boundary premise. -/
theorem norm_ring_unit_symbol_mem_constant_range (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    milnorKNorm (RatFunc k) E (n + 1)
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) (n + 1)) :=
  norm_mem_constant_range_of_totalResidue_zero k S E n _ (totalResidue_ring_units S E n a)

end Stacks.Chow.DedekindResidue
