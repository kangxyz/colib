/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteAdjoinRoot
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRSquareEquiv
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation

/-!
# The chosen finite norm over the original complete DVR

The actual primitive-element presentation transports the proved quotient-field
square to the original finite field extension and the specified integral closure.
The integral equivalence is the literal restriction of the field equivalence,
followed by the native uniqueness equivalence for the specified closure.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/Complete.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 55–88.
The original complete-base and residue-characteristic-zero hypotheses are retained.
No assumed norm square, normality, prime degree or Milnor torsion-freeness occurs.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

variable (R F E S : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra R E] [IsScalarTower R F E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E]

/-- Every actual finite extension satisfies the norm-residue square in its specified
finite DVR integral closure of the original complete residue-characteristic-zero base. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x) := by
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation F E
  let ε := f.symm
  let A := AdjoinRoot (poly p)
  let B := integralClosure R A
  let C := integralClosure R E
  have : FiniteDimensional F A := (AdjoinRoot.powerBasis' (monic p)).finite
  have : IsDiscreteValuationRing B := integralClosure_isDiscreteValuationRing R F A
  have : IsLocalHom (algebraMap R B) := integralClosure_isLocalHom R F A
  have : IsFractionRing B A :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F A B
  have : Module.Finite (ResidueField R) (ResidueField B) :=
    integralClosure_residue_finite R F A
  let j : B ≃ₐ[R] S := (ε.restrictScalars R).mapIntegralClosure.trans
    (IsIntegralClosure.equiv R C E S)
  have hj (b : B) : ε (algebraMap B A b) = algebraMap S E (j b) := by
    dsimp only [j, AlgEquiv.trans_apply]
    rw [IsIntegralClosure.algebraMap_equiv]
    rfl
  exact dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv j ε hj n
    (dvrMilnorTameSymbol'_milnorKNorm_complete_adjoinRoot R F p n) x

/-- The same complete-DVR compatibility as equality of the original additive maps. -/
theorem dvrMilnorTameSymbol'_comp_milnorKNorm_complete (n : ℕ) :
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      (milnorKNorm (ResidueField R) (ResidueField S) n).comp
        (dvrMilnorTameSymbol' S E n) := by
  apply AddMonoidHom.ext
  intro x
  exact dvrMilnorTameSymbol'_milnorKNorm_complete R F E S n x

end Stacks.Chow

end

attribute [colib_tag "COL-1001",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Norm/FiniteExtension/Complete.lean:59-88" "adaptation"
    "The complete DVR norm–residue identity on the native Milnor groups"]
  Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_complete
  Stacks.Chow.dvrMilnorTameSymbol'_comp_milnorKNorm_complete
