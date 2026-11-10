/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointResidues

/-! Consumers of the full affine endpoint residue formulas. -/

noncomputable section
open Polynomial IsDedekindDomain IsLocalRing Stacks.Chow
open Stacks.Chow.DedekindResidue Stacks.Chow.PolynomialDedekindResidue
open MonicIrreducibleOfDegree
attribute [local instance] Classical.decEq Ideal.Quotient.field polynomialPointResidueCharZero

section Local
variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra R E] [IsFractionRing R E]

example (n : ℕ) (a : Fin n → Rˣ) (b : Eˣ) :
    dvrMilnorTameSymbol' R E n
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap R E).toMonoidHom ∘ a) b)) =
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible R).choose_spec b •
        milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  dvrMilnorTameSymbol'_ringUnits_last R E n a b

example (a : Fin 0 → Rˣ) (b : Eˣ) :
    dvrMilnorTameSymbol' R E 0
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap R E).toMonoidHom ∘ a) b)) =
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible R).choose_spec b •
        milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  dvrMilnorTameSymbol'_ringUnits_last R E 0 a b

end Local

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

example (p : MonicIrreduciblePoint k) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    milnorKTotalResidue k n (milnorKNorm (RatFunc k) E (n + 1) x) p =
      milnorKTheoryMap (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom n
        (∑ q : AdicCompletion.IdealBranch ((point p).asIdeal.map (algebraMap k[X] S)),
          branchCoordinateNorm k[X] S (point p) n q
            (dvrMilnorTameSymbol'
              (Localization.AtPrime (branchPoint k[X] S (point p) q).asIdeal) E n x)) :=
  residueAt_norm_eq_original_branch_sum k S E p n x

example (p : MonicIrreduciblePoint k) (n : ℕ) (a : Fin n → Sˣ) (b : Eˣ) :
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
                  (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ a))) :=
  residueAt_norm_unit_symbol_last k S E p n a b
