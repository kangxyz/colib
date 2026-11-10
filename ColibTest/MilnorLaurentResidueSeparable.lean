/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidueSeparable
import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidue

open Polynomial IsLocalRing Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

noncomputable section

universe u

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

-- No CharZero or PerfectField hypothesis is supplied.
example (hsep : (poly p).Separable) (hp : d.Prime)
    (y : MilnorKRing
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))))) :
    milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (milnorKNormRing (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) y) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom y) :=
  milnorKNormRing_powerSeriesResidueEquiv_of_separable p hsep hp y

example (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (y : MilnorKTheory
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m y) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m y) :=
  milnorKNorm_powerSeriesResidueEquiv_of_separable p hsep hp m y

example
    (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) m) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_mem_mixedSpan p hsep hp m x hx

example
    (hsep : (poly p).Separable) (hp : d.Prime) (hd : d ≤ 2) (m : ℕ)
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
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_degree_le_two p hsep hp hd m x

example
    (hsep : (poly p).Separable) (hp : d.Prime)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom 0
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) 0
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1 x)) =
      milnorKNorm k (AdjoinRoot (poly p)) 0
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom 0
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 0 x)) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_degree_one p hsep hp x

