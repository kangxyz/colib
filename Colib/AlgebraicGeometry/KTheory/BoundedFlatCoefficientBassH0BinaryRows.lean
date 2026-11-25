/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0CommonReference
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionRightRows

/-!
# The signed first and middle right binary rows of the native Bass H₀ comparison

The two charts share the same Laurent total reference and retain each of
their original complete binary rows. Adapted from `BassH0BinaryRows.lean`
in Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
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

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- The first projection reference for the chart `α`, anchored at the common Laurent total. -/
abbrev chartProjectionFirstRef := projectionFirstReference
  (polynomialProjection P a) (coefficientMap P (α.app a))
  (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a) ha
  (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v)

/-- The middle projection reference for `α`, using chart naturality for the composite `u ≫ v`. -/
abbrev chartProjectionMiddleRef := projectionMiddleReference
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app c))
  (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
  (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
  (coefficientMap_naturality_of_natTrans P α (u ≫ v))
    (laurentProjection P a) ha
  (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v)

/-- The reference from the common Laurent total to the precomposed first binary source row. -/
def chartFirstRowReference :
    (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor ≅
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a) ≫
      BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P (α.app a))).hom.toFunctor :=
  rightRowReference (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P (α.app a)) (polynomialProjection P a) (chartProjectionFirstRef P u v α ha)

/-- The reference from the common Laurent total to the precomposed middle binary source row. -/
def chartMiddleRowReference :
    (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor ≅
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a) ≫
      BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))).hom.toFunctor :=
  rightRowReference (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))) (polynomialProjection P a)
    (chartProjectionMiddleRef P u v α ha)

/-- The exact first right row of the original single-arrow chart projection comparison. -/
theorem chart_first_row (i : Fin 3) :
    reanchorNode (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BoundedFlatCoefficientBassH0Diagram.chartNodes P (u ≫ v) α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (coefficientMap P (α.app a))
      (chartFirstRowReference P u v α ha) i :=
  projection_first_right_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P c) (coefficientMap P (α.app c))
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (polynomialProjection_naturality P (u ≫ v))
    (coefficientMap_naturality_of_natTrans P α (u ≫ v))
      (laurentProjection P a) ha
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v) i

/-- The exact middle right row retains the original chart naturality transport and raw node. -/
theorem chart_middle_row (i : Fin 3) :
    reanchorNode (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BoundedFlatCoefficientBassH0Diagram.chartNodes P (u ≫ v) α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v α ha) i :=
  projection_middle_right_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P c) (coefficientMap P (α.app c))
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (polynomialProjection_naturality P (u ≫ v))
    (coefficientMap_naturality_of_natTrans P α (u ≫ v))
      (laurentProjection P a) ha
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v) i

/-- The complete original plus H0 first binary row in the common reference. -/
theorem plus_first_row (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((underToLaurent R).app a))
      (chartFirstRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have he := reanchorNode_congr (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.plus_nodes P (u ≫ v)
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_first_row P u v (underToLaurent R) (laurentPlus_projection P a) i)

/-- The complete original plus H0 middle binary row in the common reference. -/
theorem plus_middle_row (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have he := reanchorNode_congr (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.plus_nodes P (u ≫ v)
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_middle_row P u v (underToLaurent R) (laurentPlus_projection P a) i)

/-- The complete original minus H0 first binary row in the common reference. -/
theorem minus_first_row (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((underToLaurentInvert R).app a))
      (chartFirstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have he := reanchorNode_congr (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.minus_nodes P (u ≫ v)
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_first_row P u v (underToLaurentInvert R) (laurentMinus_projection P a) i)

/-- The complete original minus H0 middle binary row in the common reference. -/
theorem minus_middle_row (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have he := reanchorNode_congr (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.minus_nodes P (u ≫ v)
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_middle_row P u v (underToLaurentInvert R) (laurentMinus_projection P a) i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge
