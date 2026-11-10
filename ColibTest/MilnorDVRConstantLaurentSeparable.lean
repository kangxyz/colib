/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRConstantPrimeSeparable
import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentPrimeSeparable

noncomputable section

open Polynomial IsLocalRing Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

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

/-- The general Japanese-DVR theorem specializes to the literal original Laurent
square, including degree equal to the characteristic and every homogeneous degree. -/
example (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
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
  let _ : SMul k (LaurentSeries k) := Algebra.toSMul
  let _ : Module k (LaurentSeries k) := Algebra.toModule
  have : IsScalarTower k (PowerSeries k) (LaurentSeries k) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable (ResidueField (PowerSeries k))
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) :=
    isSeparable_powerSeriesRoot_residue p hsep
  exact dvrMilnorTameSymbol'_milnorKNorm_of_japanese_separable_constant_cover
    k (PowerSeries k)
    (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) (LaurentSeries k)
    p (PowerSeries.isJapaneseRing_of_field k) hsep hp n x

end
