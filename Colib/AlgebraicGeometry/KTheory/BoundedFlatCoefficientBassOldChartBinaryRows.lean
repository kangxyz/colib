/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectRectangleInitialBinaryRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassMergedBoundarySimplex

/-!
# The old composition charts retain their actual binary rows

Both the positive and inverse-coordinate chart nodes in the 44-simplex keep the complete
original reference comparison for the outer and initial binary normalizations.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassOldChartBinaryRows.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOldChartBinaryRows

open BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectRectangleInitialBinaryRow
open BoundedFlatCoefficientBassOverlap
open BoundedFlatCoefficientBassChartBottomReferences (laurentComposite)
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The common-reference isomorphism for the original chart's precomposed outer binary row. -/
def oldOuterRowReference : (commonReference P u v).hom.toFunctor ≅
    (projectionMap P (a := a) ≫ BoundedFlatPerfectBinarySimplex.sourceMap
      (laurentComposite P u v) (coefficientMap P (α.app a))).hom.toFunctor :=
  rectangleOuterReference
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α u).symm
    (coefficientMap_naturality_of_natTrans P α v).symm
    (commonReference P u v) (projectionMap P (a := a))
    (commonToChartReference P u v α hc)

/-- The common-reference isomorphism for the original chart's precomposed initial binary row. -/
def oldInitialRowReference : (commonReference P u v).hom.toFunctor ≅
    (projectionMap P (a := a) ≫ BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))).hom.toFunctor :=
  commonToChartReference P u v α hc

/-- The original chart's entire outer binary row keeps its actual geometric transport. -/
theorem old_chart_outer_row (i : Fin 3) :
    chartOverlapNodes P u v α hc (outerIndex i) =
      preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
        (laurentComposite P u v) (coefficientMap P (α.app a))
        (oldOuterRowReference P u v α hc) i :=
  rectangle_outer_row
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α u).symm
    (coefficientMap_naturality_of_natTrans P α v).symm
    (commonReference P u v) (projectionMap P (a := a))
    (commonToChartReference P u v α hc) i

/-- The whole initial row uses the original two polynomial coefficient factors. -/
theorem old_chart_initial_row (i : Fin 3) :
    chartOverlapNodes P u v α hc (initialIndex i) =
      preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
        (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u))
        (oldInitialRowReference P u v α hc) i :=
  rectangle_initial_row
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α u).symm
    (coefficientMap_naturality_of_natTrans P α v).symm
    (commonReference P u v) (projectionMap P (a := a))
    (commonToChartReference P u v α hc) i

/-- Every old merged plus chart node retains its complete original reference. -/
theorem old_plus_node (i : Fin 18) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (plusFace.toOrderHom i)) =
      chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c) i := by
  rw [BoundedFlatCoefficientBassReferenceMerge.chart_nodes]
  change BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
    (Fin.castAdd 15 (Fin.castAdd 18 i)) = _
  unfold BoundedFlatCoefficientBassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BoundedFlatCoefficientBassOverlap.nodes
  rw [Fin.addCases_left]

/-- The original plus chart's entire outer row survives the old dependent-node merge. -/
theorem old_plus_outer_row (i : Fin 3) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (plusFace.toOrderHom (outerIndex i))) =
    preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
      (laurentComposite P u v)
      (coefficientMap P ((underToLaurent R).app a))
      (oldOuterRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) i := by
  rw [old_plus_node]
  exact old_chart_outer_row P u v (underToLaurent R) (laurentPlus_projection P c) i

/-- The original plus chart's entire initial row survives the old dependent-node merge. -/
theorem old_plus_initial_row (i : Fin 3) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (plusFace.toOrderHom (initialIndex i))) =
    preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
      (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (oldInitialRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) i := by
  rw [old_plus_node]
  exact old_chart_initial_row P u v (underToLaurent R) (laurentPlus_projection P c) i

/-- Every old merged minus chart node retains its complete original reference. -/
theorem old_minus_node (i : Fin 18) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (minusFace.toOrderHom i)) =
      chartOverlapNodes P u v (underToLaurentInvert R)
        (laurentMinus_projection P c) i := by
  rw [BoundedFlatCoefficientBassReferenceMerge.chart_nodes]
  change BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
    (Fin.castAdd 15 (Fin.natAdd 18 i)) = _
  unfold BoundedFlatCoefficientBassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BoundedFlatCoefficientBassOverlap.nodes
  rw [Fin.addCases_right]

/-- The original minus chart's entire outer row survives the old dependent-node merge. -/
theorem old_minus_outer_row (i : Fin 3) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (minusFace.toOrderHom (outerIndex i))) =
    preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
      (laurentComposite P u v)
      (coefficientMap P ((underToLaurentInvert R).app a))
      (oldOuterRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) i := by
  rw [old_minus_node]
  exact old_chart_outer_row P u v (underToLaurentInvert R) (laurentMinus_projection P c) i

/-- The original minus chart's entire initial row survives the old dependent-node merge. -/
theorem old_minus_initial_row (i : Fin 3) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (minusFace.toOrderHom (initialIndex i))) =
    preBinaryNodes (commonReference P u v) (projectionMap P (a := a))
      (coefficientMap P ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (oldInitialRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) i := by
  rw [old_minus_node]
  exact old_chart_initial_row P u v (underToLaurentInvert R) (laurentMinus_projection P c) i

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOldChartBinaryRows
