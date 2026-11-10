/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalOriginResidueSeparable

noncomputable section

open Polynomial IsLocalRing Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

variable {k : Type u} [Field k] {d : ℕ}

local instance (p : MonicIrreducibleOfDegree k d) : Fact (poly p).Monic :=
  ⟨monic p⟩

local instance (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  [Normal k (AdjoinRoot (poly p))]

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) =
      milnorKNorm (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n
        (milnorKTheoryMap
          (RingHom.comp
            (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
              ((poly p).map (RatFunc.C : k →+* RatFunc k))
              ((poly p).map (algebraMap k (LaurentSeries k))) (by
                rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom)
          n x) :=
  milnorKNorm_ratFunc_map_laurentSeries_of_separable p hsep hp n x

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
          (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
            (RatFunc (AdjoinRoot (poly p))) n x)) :=
  dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin_of_separable p hsep hp n x

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom n x) =
      milnorKTheoryMap (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) :=
  milnorKNorm_ratFunc_map_chartInversion_of_separable p hsep hp n x

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    infinityResidue n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x) =
      milnorKNorm k (AdjoinRoot (poly p)) n (infinityResidue n x) :=
  infinityResidue_milnorKNorm_ratFunc_of_separable p hsep hp n x

example (hp : d.Prime)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) 1) :
    infinityResidue 0
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) 1 x) =
      milnorKNorm k (AdjoinRoot (poly p)) 0 (infinityResidue 0 x) :=
  infinityResidue_milnorKNorm_ratFunc_of_separable p hsep hp 0 x
