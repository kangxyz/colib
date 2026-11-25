/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Diagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows

/-!
# Source and target binary rows of the coefficient comparison

Each original Laurent chart retains its complete binary normalization nodes, rather than
only the endpoints of its projection comparison.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/H0ProjectionBoundaryRows.lean`
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
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0ProjectionBoundaryRows

open BoundedFlatPerfectProjectionBinaryRows
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- The functor equality identifying the H0 reference with the chart's source triple. -/
abbrev sourceAnchor := BoundedFlatPerfectProjectionReference.anchor (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map w))
  (laurentProjection P a) ha

/-- The reference from the H0 source to the last triple, using the projection anchor and both
naturality squares. -/
abbrev lastReference := nativeLastReference
  (polynomialProjection P a) (coefficientMap P (α.app a))
  (polynomialProjection P b) (coefficientMap P (α.app b))
  (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientMap P ((laurentUnderFunctor R).map w))
  (polynomialProjection_naturality P w)
  (coefficientMap_naturality_of_natTrans P α w)
    (laurentProjection P a) ha

/-- The reference from the H0 source to the target binary row precomposed by the coefficient map
of `w`. -/
abbrev targetRowReference := rightRowReference (BoundedFlatCoefficientBassH0Diagram.reference P w)
  (coefficientMap P (α.app b)) (polynomialProjection P b) (coefficientMap P w)
  (lastReference P w α ha)

theorem chart_source_column (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.chartNodes P w α ha (rectangleLeftIndex i) =
      binaryColumnNode (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P (α.app a)) (polynomialProjection P a) (sourceAnchor P w α ha) i :=
  native_source_column
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (polynomialProjection_naturality P w)
    (coefficientMap_naturality_of_natTrans P α w)
      (laurentProjection P a) ha i

theorem chart_target_row (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.chartNodes P w α ha
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      preBinaryNodes (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (normalizedMap (coefficientMap P w))
        (coefficientMap P (α.app b)) (polynomialProjection P b)
        (targetRowReference P w α ha) i :=
  native_target_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (polynomialProjection_naturality P w)
    (coefficientMap_naturality_of_natTrans P α w)
      (laurentProjection P a) ha i

/-- The full original plus source binary row retains its actual references. -/
theorem plus_source (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.nodes P w
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((underToLaurent R).app a)) (polynomialProjection P a)
        (sourceAnchor P w (underToLaurent R) (laurentPlus_projection P a)) i :=
  (BoundedFlatCoefficientBassH0Diagram.plus_nodes P w (rectangleLeftIndex i)).trans
    (chart_source_column P w (underToLaurent R) (laurentPlus_projection P a) i)

/-- The full original plus target binary row retains its actual references. -/
theorem plus_target (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.nodes P w
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
      preBinaryNodes (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (normalizedMap (coefficientMap P w))
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b)
        (targetRowReference P w (underToLaurent R) (laurentPlus_projection P a)) i :=
  (BoundedFlatCoefficientBassH0Diagram.plus_nodes P w
    (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))).trans
    (chart_target_row P w (underToLaurent R) (laurentPlus_projection P a) i)

/-- The full original minus source binary row retains its actual references. -/
theorem minus_source (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.nodes P w
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((underToLaurentInvert R).app a)) (polynomialProjection P a)
        (sourceAnchor P w (underToLaurentInvert R) (laurentMinus_projection P a)) i :=
  (BoundedFlatCoefficientBassH0Diagram.minus_nodes P w (rectangleLeftIndex i)).trans
    (chart_source_column P w (underToLaurentInvert R) (laurentMinus_projection P a) i)

/-- The full original minus target binary row retains its actual references. -/
theorem minus_target (i : Fin 3) :
    BoundedFlatCoefficientBassH0Diagram.nodes P w
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
      preBinaryNodes (BoundedFlatCoefficientBassH0Diagram.reference P w)
        (normalizedMap (coefficientMap P w))
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b)
        (targetRowReference P w (underToLaurentInvert R) (laurentMinus_projection P a)) i :=
  (BoundedFlatCoefficientBassH0Diagram.minus_nodes P w
    (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))).trans
    (chart_target_row P w (underToLaurentInvert R) (laurentMinus_projection P a) i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0ProjectionBoundaryRows
