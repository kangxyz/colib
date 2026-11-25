/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSquareFamilies
public import Colib.KTheory.Waldhausen.Iterated.RealizationSimplexComposition

/-!
# Simultaneous polynomial and Laurent square paths for the Bass composition

The positive and inverse products retain their independent times; the inverse
component reverses exactly the polynomial time. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH1Components.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- Actual composition of two independently varying original square diagrams. -/
def chartProduct := CommonReferenceProduct.simplex
  (BoundedFlatCoefficientSquareFamilies.polynomialSource P u)
  (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).1)
  (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).2)
  (BoundedFlatCoefficientSquareFamilies.chartSource P v α)
  (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).1)
  (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).2)

/-- The real realization-product parameter composes both whole families at every original level. -/
theorem chart_product_family (n : ℕ) (z w : StdSimplex ℝ (Fin 5))
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v α) n
      (SimplexGrid.parameter.{u + 1} 4 4 (z, w), x) =
      prespectrumSimplexFamily (BoundedFlatCoefficientSquareFamilies.chartSimplex P v α) n
        (w, prespectrumSimplexFamily
          (BoundedFlatCoefficientSquareFamilies.polynomialSimplex P u) n (z, x)) :=
  CommonReferenceProduct.prespectrum_comp _ _ _ _ _ _ n x z w

/-- Both scalar times are independent in the positive product piece. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 4
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter z.2,
      BoundedFlatPerfectNativeSquareFiveSimplex.parameter z.1), by fun_prop⟩

/-- The inverse piece retains the original reversal of the polynomial-square time. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 4
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter (unitInterval.symm z.2),
      BoundedFlatPerfectNativeSquareFiveSimplex.parameter z.1), by fun_prop⟩

/-- Whole first span-cylinder segment after the independently moving positive v-square. -/
theorem plus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v (underToLaurent R)) n
      (plusParameter.{u} (s, t), x) =
      (boundedAboveFlatCoefficientPlusSquareHomotopy P v).level n
        (s, (boundedAboveFlatCoefficientPolynomialSquareHomotopy P u).level n (t, x)) := by
  change prespectrumSimplexFamily (chartProduct P u v (underToLaurent R)) n
    (SimplexGrid.parameter 4 4 (_, _), x) = _
  rw [chart_product_family, BoundedFlatCoefficientSquareFamilies.polynomial_native,
    BoundedFlatCoefficientSquareFamilies.plus_native]

/-- Whole final span-cylinder segment, retaining its reverse polynomial and inverse-chart values. -/
theorem minus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v (underToLaurentInvert R)) n
      (minusParameter.{u} (s, t), x) =
      (boundedAboveFlatCoefficientMinusSquareHomotopy P v).level n
        (s, (boundedAboveFlatCoefficientPolynomialSquareHomotopy P u).level n
          (unitInterval.symm t, x)) := by
  change prespectrumSimplexFamily (chartProduct P u v (underToLaurentInvert R)) n
    (SimplexGrid.parameter 4 4 (_, _), x) = _
  rw [chart_product_family, BoundedFlatCoefficientSquareFamilies.polynomial_native,
    BoundedFlatCoefficientSquareFamilies.minus_native]

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components
