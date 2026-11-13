/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineUnitSymbolResidues
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineNormSpecialization

/-!
# All original affine branches at native polynomial places

Adapted from Aglib `Dedekind/AffineEndpointResidues.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 29–65.
The native polynomial coordinate of `milnorKTotalResidue` replaces only the
separate Aglib polynomial-residue model. Its comparison with the actual
Dedekind residue is the proved `PolynomialDedekindResidue.totalResidue_point`.
Every original branch, order and reduced tuple is retained.
-/

@[expose] public noncomputable section
namespace Stacks.Chow.DedekindResidue

open Polynomial PolynomialDedekindResidue IsLocalRing IsDedekindDomain
open MonicIrreducibleOfDegree
attribute [local instance] Classical.decEq Ideal.Quotient.field

universe u
variable (k S E : Type u) [Field k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- Every actual polynomial-point residue field has the characteristic of the base. -/
theorem polynomialPointResidueCharZero [CharZero k] (p : HeightOneSpectrum k[X]) :
    CharZero (ResidueField (Localization.AtPrime p.asIdeal)) :=
  charZero_of_injective_algebraMap
    (algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))).injective

/-- The native polynomial residue of the norm is the full original branch sum. -/
theorem residueAt_norm_eq_original_branch_sum (p : MonicIrreduciblePoint k)
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    milnorKTotalResidue k n (milnorKNorm (RatFunc k) E (n + 1) x) p =
      milnorKTheoryMap (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom n
        (∑ q : AdicCompletion.IdealBranch ((point p).asIdeal.map (algebraMap k[X] S)),
          branchCoordinateNorm k[X] S (point p) n q
            (dvrMilnorTameSymbol'
              (Localization.AtPrime (branchPoint k[X] S (point p) q).asIdeal) E n x)) := by
  rw [milnorKTheoryMap_eq_transport, ← PolynomialDedekindResidue.totalResidue_point,
    totalResidue_milnorKNorm k[X] S (RatFunc k) E, residuePushforward_apply]
  rfl

/-- Appending an arbitrary original-field parameter keeps every actual branch order. -/
theorem residueAt_norm_unit_symbol_last (p : MonicIrreduciblePoint k)
    (n : ℕ) (a : Fin n → Sˣ) (b : Eˣ) :
    milnorKTotalResidue k n (milnorKNorm (RatFunc k) E (n + 1)
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ a) b))) p =
      milnorKTheoryMap (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom n
        (∑ q : AdicCompletion.IdealBranch ((point p).asIdeal.map (algebraMap k[X] S)),
          let Q := branchPoint k[X] S (point p) q
          branchCoordinateNorm k[X] S (point p) n q
            (dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
              (Localization.AtPrime Q.asIdeal)).choose_spec b •
              milnorKTupleSymbol (Units.map
                ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
                  (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ a))) := by
  rw [residueAt_norm_eq_original_branch_sum k S E]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [DedekindResidue.residue_ring_units_last]

end Stacks.Chow.DedekindResidue
