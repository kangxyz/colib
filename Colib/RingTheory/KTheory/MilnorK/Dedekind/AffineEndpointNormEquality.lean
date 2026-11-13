/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointResidues
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Actual order-weighted endpoint norm sums

Adapted from Aglib `Dedekind/AffineEndpointNormEquality.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 33–82.
The ordered last-slot product is the existing `milnorKMulSymbol`. Its norm
projection formula is proved by the native whole-ring right projection formula.
The endpoint sum uses every original ideal branch with its full integer order.
-/

@[expose] public noncomputable section
namespace Stacks.Chow

universe u

/-- Native norms commute with right multiplication by a base-field symbol. -/
theorem milnorKNorm_mulSymbol (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (n : ℕ) (x : MilnorKTheory E n) (b : Fˣ) :
    milnorKNorm F E (n + 1)
      (milnorKMulSymbol E n (Units.map (algebraMap F E).toMonoidHom b) x) =
      milnorKMulSymbol F n b (milnorKNorm F E n x) := by
  apply Subtype.ext
  simp only [coe_milnorKNorm, coe_milnorKMulSymbol]
  rw [← milnorKRingMap_symbol, milnorKNormRing_mul_map]

namespace DedekindResidue

open Polynomial PolynomialResidue PolynomialDedekindResidue IsLocalRing IsDedekindDomain
attribute [local instance] Classical.decEq

variable (k S E : Type u) [Field k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The literal linear polynomial, in the existing native polynomial-point index. -/
abbrev endpointPolynomial (a : k) : MonicIrreduciblePoint k :=
  ⟨1, Polynomial.X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩

/-- The actual linear parameter in the unchanged function field. -/
def endpointParameter (a : k) : Eˣ :=
  Units.map (algebraMap (RatFunc k) E).toMonoidHom
    (polyUnit (irreducible_X_sub_C a).ne_zero)

/-- Every original endpoint branch, with its actual order and reduced global tuple. -/
def endpointWeightedResidueSum (a : k) (n : ℕ) (u : Fin n → Sˣ) : MilnorKTheory k n :=
  milnorKTheoryMap (linearResidueEquiv a).toRingHom n
    (∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
      branchCoordinateNorm k[X] S (point (endpointPolynomial k a)) n q
        (dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
          (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
          milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)))

/-- The evaluated norm residue is exactly the full order-weighted original branch sum. -/
theorem linearResidue_norm_unit_symbol_last (a : k) (n : ℕ) (u : Fin n → Sˣ) :
    linearResidue a n (milnorKNorm (RatFunc k) E (n + 1)
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ u)
        (endpointParameter k E a)))) = endpointWeightedResidueSum k S E a n u := by
  let p := point (endpointPolynomial k a)
  let e : ResidueField (Localization.AtPrime p.asIdeal) →+* k :=
    (linearResidueEquiv a).toRingHom
  let T := milnorKTheoryMap e n
  let x : MilnorKTheory E (n + 1) :=
    milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ u)
      (endpointParameter k E a))
  have hlocal := congrArg T
    (PolynomialDedekindResidue.totalResidue_point_eq_affineLineResidue
      (endpointPolynomial k a) n (milnorKNorm (RatFunc k) E (n + 1) x)).symm
  have hsum : totalResidue k[X] (RatFunc k) n
      (milnorKNorm (RatFunc k) E (n + 1) x) p =
      ∑ q : AdicCompletion.IdealBranch (p.asIdeal.map (algebraMap k[X] S)),
        let Q := branchPoint k[X] S p q
        branchCoordinateNorm k[X] S p n q
          (dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
            (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
            milnorKTupleSymbol (Units.map
              ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
                (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) := by
    rw [totalResidue_milnorKNorm k[X] S (RatFunc k) E, residuePushforward_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [totalResidue_apply, residue_ring_units_last]
  exact hlocal.trans (congrArg T hsum)

/-- The full actual endpoint sum is the literal specialization of the actual norm. -/
theorem endpointWeightedResidueSum_eq_specialization (a : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    endpointWeightedResidueSum k S E a (n + 1) u =
      linearSpecialization a (n + 1) (milnorKNorm (RatFunc k) E (n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) := by
  rw [← linearResidue_norm_unit_symbol_last, ← milnorKMulSymbol_tupleSymbol]
  unfold endpointParameter
  rw [milnorKNorm_mulSymbol]
  exact linearResidue_norm_ring_unit_symbol_mulSymbol k S E a n u

/-- Any two full original endpoint sums agree in every positive degree. -/
theorem endpointWeightedResidueSum_eq (a b : k) (n : ℕ) (u : Fin (n + 1) → Sˣ) :
    endpointWeightedResidueSum k S E a (n + 1) u =
      endpointWeightedResidueSum k S E b (n + 1) u := by
  rw [endpointWeightedResidueSum_eq_specialization,
    endpointWeightedResidueSum_eq_specialization]
  exact linearSpecialization_norm_ring_unit_symbol_eq k S E a b n u

end DedekindResidue
end Stacks.Chow
