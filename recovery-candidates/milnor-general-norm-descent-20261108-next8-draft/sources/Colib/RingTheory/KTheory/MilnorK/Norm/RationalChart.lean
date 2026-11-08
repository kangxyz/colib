/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstant
public import Colib.AlgebraicGeometry.ProjectiveLine.RootChartInversion

/-!
# Native normal-prime chosen norm and the actual projective chart change

The original chosen norm on the rational function field of a normal prime-degree
root field commutes with the actual projectiveLineChartInversion. This uses the
proved literal constant-polynomial presentation and its exact coefficient square.
No separate rational-function norm or chart-change map is introduced.

This is the input needed to transport a future finite linear residue square to
infinity. It is not itself a finite-place or infinity residue square.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] [CharZero k] {d : ℕ}
  (p : MonicIrreducibleOfDegree k d)

local instance : Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance : Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

/-- The native chosen rational norm commutes with the original projective chart
inversion, for every whole-ring class in normal prime degree and characteristic zero. -/
theorem milnorKNormRing_ratFunc_map_chartInversion (hp : d.Prime)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom x) =
      milnorKRingMap (projectiveLineChartInversion k).toRingHom
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) := by
  rw [milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp,
    milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp, milnorKRingMap_comp_apply]
  have hcomp : (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom.comp
      (projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom =
      (AdjoinRoot.map (projectiveLineChartInversion k).toRingHom
        ((poly p).map RatFunc.C) ((poly p).map RatFunc.C)
        (by rw [map_ratFunc_C_chartInversion]; exact dvd_rfl)).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom := by
    apply RingHom.ext
    intro z
    exact rationalCoefficientAlgEquiv_symm_chartInversion (poly p) (monic p) z
  rw [hcomp, ← milnorKRingMap_comp_apply]
  exact (simpleMilnorNorm_map_of_poly_eq_map
    (projectiveLineChartInversion k).toRingHom p.ratFunc p.ratFunc
    (map_ratFunc_C_chartInversion (poly p)).symm
    (milnorKRingMap (AdjoinRoot.rationalCoefficientAlgEquiv
      (poly p) (monic p)).symm.toRingHom x)).symm

end Stacks.Chow
