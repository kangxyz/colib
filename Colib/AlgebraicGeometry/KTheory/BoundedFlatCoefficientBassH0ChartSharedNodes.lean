/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0LaurentSharedNodes

/-!
# The remaining shared nodes of H₀ and the original Bass 44-simplex

The polynomial rows are matched through their already identified full source
and the actual equality of polynomial coefficient maps. The other two
nodes are the raw intermediate terms of the signed bottom binary columns.
Adapted from `BinaryRowMatching.lean` and `BassH0ChartSharedNodes.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` in Quillen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge

open BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectRectangleInitialBinaryRow
open BoundedFlatCoefficientBassOldChartBinaryRows

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original plus polynomial row is determined by the full common source node. -/
theorem plus_polynomial_rows (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (initialIndex i))) := by
  have hs := (plus_middle_row P u v 0).symm.trans
    ((shared_positive_center_node P u v).trans (old_plus_initial_row P u v 0))
  have hr := preBinaryNodes_source_congr
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (coefficientMap P ((underToLaurent R).app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    rfl (polynomial_composite P u v)
    (chartMiddleRowReference P u v (underToLaurent R) (laurentPlus_projection P a))
    (oldInitialRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) hs i
  exact (plus_middle_row P u v i).trans (hr.trans (old_plus_initial_row P u v i).symm)

/-- The original minus polynomial row is determined by the full common source node. -/
theorem minus_polynomial_rows (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (initialIndex i))) := by
  have hs := (minus_middle_row P u v 0).symm.trans
    ((shared_negative_center_node P u v).trans (old_minus_initial_row P u v 0))
  have hr := preBinaryNodes_source_congr
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (coefficientMap P ((underToLaurentInvert R).app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    rfl (polynomial_composite P u v)
    (chartMiddleRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a))
    (oldInitialRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) hs i
  exact (minus_middle_row P u v i).trans (hr.trans (old_minus_initial_row P u v i).symm)

/-- Full shared node H₀[12] = 44[1], including its anchored reference. -/
theorem shared_positive_polynomial_raw_node :
    nodes P u v 12 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 1 :=
  plus_polynomial_rows P u v 1

/-- Full shared node H₀[13] = 44[2], including its anchored reference. -/
theorem shared_positive_polynomial_target_node :
    nodes P u v 13 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 2 :=
  plus_polynomial_rows P u v 2

/-- Full shared node H₀[23] = 44[25], including its anchored reference. -/
theorem shared_negative_polynomial_raw_node :
    nodes P u v 23 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 25 :=
  minus_polynomial_rows P u v 1

/-- Full shared node H₀[24] = 44[26], including its anchored reference. -/
theorem shared_negative_polynomial_target_node :
    nodes P u v 24 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 26 :=
  minus_polynomial_rows P u v 2

/-- Full shared node H₀[3] = 44[18], including its anchored reference. -/
theorem shared_positive_bottom_raw_node :
    nodes P u v 3 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 18 :=
  positive_source_nodes P u v 1

/-- Full shared node H₀[14] = 44[39], including its anchored reference. -/
theorem shared_negative_bottom_raw_node :
    nodes P u v 14 = BoundedFlatCoefficientBassReferenceMerge.nodes P u v 39 :=
  negative_source_nodes P u v 0

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge
