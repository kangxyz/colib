/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointBaseNorm

/-! Consumers of the full affine endpoint norm equality. -/

noncomputable section
open Polynomial IsDedekindDomain IsLocalRing Stacks.Chow
open Stacks.Chow.DedekindResidue Stacks.Chow.PolynomialDedekindResidue
open Stacks.Chow.PolynomialResidue
attribute [local instance] Classical.decEq polynomialPointResidueCharZero

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

example : Function.Surjective (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) 0) :=
  constant_restriction_zero_surjective k

example (a b : k) (n : ℕ) (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u = endpointWeightedResidueSum k S E b n u :=
  endpointWeightedResidueSum_eq_all k S E a b n u

example (a b : k) (u : Fin 0 → Sˣ) :
    endpointWeightedResidueSum k S E a 0 u = endpointWeightedResidueSum k S E b 0 u :=
  endpointWeightedResidueSum_eq_all k S E a b 0 u

example (a : k) (u : Fin 0 → Sˣ) :
    endpointWeightedResidueSum k S E a 0 u =
      linearSpecialization a 0 (milnorKNorm (RatFunc k) E 0
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  endpointWeightedResidueSum_eq_specialization_all k S E a 0 u

variable [Algebra k S] [IsScalarTower k k[X] S]

local instance endpointConsumerFiniteType : Algebra.FiniteType k S :=
  Algebra.FiniteType.trans (S := k[X])
    (inferInstanceAs (Algebra.FiniteType k k[X]))
    (inferInstanceAs (Algebra.FiniteType k[X] S))

local instance endpointConsumerResidueFinite (q : HeightOneSpectrum S) :
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k S q.asIdeal

example (a : k) (n : ℕ)
    (q : AdicCompletion.IdealBranch
      ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)))
    (x : MilnorKTheory (ResidueField (Localization.AtPrime
      (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n) :
    milnorKTheoryMap (endpointResidueEquiv k a).toRingHom n
      (branchCoordinateNorm k[X] S (point (endpointPolynomial k a)) n q x) =
        milnorKNorm k (ResidueField (Localization.AtPrime
          (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n x :=
  endpoint_branchNorm_eq k S a n q x

example (a b : k) (n : ℕ) (u : Fin n → Sˣ) :
    (∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u))) =
    ∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k b)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k b)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E b) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) :=
  endpointBaseNormSum_eq_all k S E a b n u

example (a b : k) (u : Fin 0 → Sˣ) :
    (∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) 0
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u))) =
    ∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k b)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k b)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E b) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) 0
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) :=
  endpointBaseNormSum_eq_all k S E a b 0 u
