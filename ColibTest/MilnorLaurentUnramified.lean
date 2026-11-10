/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentUnramified
import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidue

open Polynomial Stacks.Chow

noncomputable section

universe u

-- No perfectness, characteristic-zero, normality or separability typeclass is supplied.
example {k E : Type u} [Field k] [Field E] (φ : k →+* E)
    (x : MilnorKTheory E 1) : x ∈ milnorKMixedSpan φ 0 :=
  mem_milnorKMixedSpan_zero φ x

example {k : Type u} [Field k] (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hd : p.natDegree ≤ 2) (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    x ∈ milnorKMixedSpan (algebraMap k (AdjoinRoot p)) m :=
  mem_milnorKMixedSpan_of_natDegree_le_two p hp hd m x

example {k : Type u} [Field k] (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hd : p.natDegree ≤ 2) (m : ℕ) :
    milnorKMixedSpan (algebraMap k (AdjoinRoot p)) m = ⊤ :=
  milnorKMixedSpan_eq_top_of_natDegree_le_two p hp hd m

example {k : Type u} [Field k] (p : k[X]) [Fact (Irreducible p)]
    (hsep : p.Separable) : Algebra.IsSeparable k (AdjoinRoot p) :=
  AdjoinRoot.isSeparable_of_polynomial_separable p hsep

-- Activate the exact native structures from the new leaf, rather than replacing
-- the Laurent or residue carriers with a comparison model.
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

open IsLocalRing Stacks.Chow.MonicIrreducibleOfDegree

variable {k : Type u} [Field k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)

-- An actual all-symbol square, not merely a check of a generation helper.
example (hd : d ≤ 2) (m : ℕ) (x : MilnorKTheory
    (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_degree_le_two p hd m x

-- An actual K1 square for an arbitrary-degree constant extension.
example (x : MilnorKTheory
    (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) 0
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1 x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) 0
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_degree_one p x

#print axioms AdjoinRoot.isSeparable_of_polynomial_separable
#print axioms Stacks.Chow.mem_milnorKMixedSpan_zero
#print axioms Stacks.Chow.mem_milnorKMixedSpan_of_natDegree_le_two
#print axioms Stacks.Chow.milnorKMixedSpan_eq_top_of_natDegree_le_two
#print axioms Stacks.Chow.irreducible_powerSeriesRoot_X
#print axioms Stacks.Chow.ramificationIdx_powerSeriesRoot_eq_one
#print axioms Stacks.Chow.separable_powerSeriesRoot_residuePolynomial
#print axioms Stacks.Chow.isSeparable_powerSeriesRoot_constant
#print axioms Stacks.Chow.isSeparable_laurentSeriesRoot
#print axioms Stacks.Chow.isSeparable_powerSeriesRoot_residue
#print axioms Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_mem_mixedSpan
#print axioms Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_degree_one
#print axioms Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_degree_le_two
