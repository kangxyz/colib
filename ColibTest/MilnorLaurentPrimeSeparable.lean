/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidue
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentPrimeSeparable

/-! Actual all-symbol consumers in arbitrary characteristic, jointly importing
all prior Laurent and new prime-separable endpoints. -/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped TensorProduct

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

attribute [local instance]
  Stacks.Chow.laurentUnramified_factMonic
  Stacks.Chow.laurentUnramified_factIrreducible
  Stacks.Chow.laurentUnramified_factIrreducibleLaurent
  Stacks.Chow.laurentUnramified_isDomain
  Stacks.Chow.laurentUnramified_isLocalRing
  Stacks.Chow.laurentUnramified_isDiscreteValuationRing
  Stacks.Chow.laurentUnramified_finitePowerSeries
  Stacks.Chow.laurentUnramified_torsionFreePowerSeries
  Stacks.Chow.laurentUnramified_isLocalHom
  Stacks.Chow.laurentUnramifiedAlgebra
  Stacks.Chow.laurentUnramified_isScalarTower
  Stacks.Chow.laurentUnramified_isFractionRing
  Stacks.Chow.laurentUnramified_finiteConstant
  Stacks.Chow.laurentUnramified_finiteLaurent

variable {k : Type u} [Field k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

/-- Consume the actual proved endpoint on its original fields and maps. -/
theorem laurentPrimeSeparable_actualConsumer1
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    ∃ a : ℕ, d.Coprime a ∧ (a : ℤ) •
      (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x) -
        milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x)) = 0 := by
  exact exists_coprime_smul_laurent_norm_residue_difference_eq_zero_of_separable p hsep hp n x

/-- Consume the actual proved endpoint on its original fields and maps. -/
theorem laurentPrimeSeparable_actualConsumer2
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_separable p hsep hp n x

/-- Consume the actual proved endpoint on its original fields and maps. -/
theorem laurentPrimeSeparable_actualConsumer3
    (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_separable p hsep hp m x

/-- The actual constant-field square over a finite base, with prime degree equal
to the positive characteristic; no prime invertibility is supplied. -/
theorem laurentPrimeSeparable_actualFiniteCharDegreeConsumer
    [Finite k] [CharP k d]
    (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_separable p hsep hp m x

end Stacks.Chow

end
