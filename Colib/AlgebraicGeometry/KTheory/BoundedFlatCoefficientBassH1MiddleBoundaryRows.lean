/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0ProjectionBoundaryRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoin

/-!
# Shared binary normalization rows in the first and middle Bass H₁ faces

The same signed Laurent chart rows occur on both components. Their full
reference nodes agree by cancellation at the already identified middle center.
Adapted from `H1MiddleBoundaryRows.lean` in the original BoundedFlat Bass proof
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CommRingCat.PolynomialLaurent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
open ModelSimplex BoundedFlatCoefficientBassH1References BoundedFlatPerfectProjectionBinaryRows
open BoundedFlatCoefficientBassH0ProjectionBoundaryRows BoundedFlatCoefficientBassH1Components
open BoundedFlatCoefficientBassOverlap
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original first component's reference on its target binary row. -/
def firstRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (commonReference P u v).hom.toFunctor ≅
      (coefficientMapModel P u ≫
        BoundedFlatPerfectBinarySimplex.sourceMap (coefficientMap P (α.app b))
          (polynomialProjection P b) ≫ laurentMap P v).hom.toFunctor :=
  firstIso P u v ≪≫ isoWhiskerRight (targetRowReference P u α ha)
    (laurentMap P v).hom.toFunctor

/-- The original middle component's reference on its source binary column. -/
def middleRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (commonReference P u v).hom.toFunctor ≅
      (coefficientMapModel P u ≫
        BoundedFlatPerfectBinarySimplex.sourceMap (coefficientMap P (α.app b))
          (polynomialProjection P b) ≫ laurentMap P v).hom.toFunctor :=
  middleIso P u v ≪≫ isoWhiskerLeft (coefficientMapModel P u).hom.toFunctor
    (eqToIso (sourceAnchor P v α hb) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ polynomialProjection P b))

/-- The original plus target row of the first component, retaining both whiskerings. -/
theorem plus_first_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    prePostNodes (commonReference P u v)
      (coefficientMapModel P u) (laurentMap P v)
      (BoundedFlatPerfectBinarySimplex.sourceMap
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (firstRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have hn := congrArg (postReferenceNode (commonReference P u v)
    (laurentMap P v) (firstIso P u v))
    (plus_target P u i)
  exact hn.trans (post_pre_node (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (targetRowReference P u (underToLaurent R) (laurentPlus_projection P a))
    (firstIso P u v) i)

/-- The original plus source column of the middle component, with the same fixed maps. -/
theorem plus_middle_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.middleNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    prePostNodes (commonReference P u v)
      (coefficientMapModel P u) (laurentMap P v)
      (BoundedFlatPerfectBinarySimplex.sourceMap
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (middleRowReference P u v (underToLaurent R) (laurentPlus_projection P b)) i := by
  have hn := congrArg (preReferenceNode (commonReference P u v)
    (coefficientMapModel P u) (middleIso P u v))
    (plus_source P v i)
  exact hn.trans (pre_post_node (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (eqToIso (sourceAnchor P v (underToLaurent R) (laurentPlus_projection P b)) ≪≫
      BoundedFlatPerfectBinarySimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((underToLaurent R).app b) ≫ polynomialProjection P b))
    (middleIso P u v) i)

/-- The complete plus binary row is shared through its proved full central reference node. -/
theorem plus_middle_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassH1References.middleNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) :=
  prePost_families_match (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (plus_first_row P u v) (plus_middle_row P u v) 0 (first_middle_center P u v) i

/-- The original minus target row of the first component, retaining both whiskerings. -/
theorem minus_first_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    prePostNodes (commonReference P u v)
      (coefficientMapModel P u) (laurentMap P v)
      (BoundedFlatPerfectBinarySimplex.sourceMap
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (firstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have hn := congrArg (postReferenceNode (commonReference P u v)
    (laurentMap P v) (firstIso P u v))
    (minus_target P u i)
  exact hn.trans (post_pre_node (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (targetRowReference P u (underToLaurentInvert R) (laurentMinus_projection P a))
    (firstIso P u v) i)

/-- The original minus source column of the middle component, with the same fixed maps. -/
theorem minus_middle_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.middleNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    prePostNodes (commonReference P u v)
      (coefficientMapModel P u) (laurentMap P v)
      (BoundedFlatPerfectBinarySimplex.sourceMap
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (middleRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P b)) i := by
  have hn := congrArg (preReferenceNode (commonReference P u v)
    (coefficientMapModel P u) (middleIso P u v))
    (minus_source P v i)
  exact hn.trans (pre_post_node (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (eqToIso (sourceAnchor P v (underToLaurentInvert R)
      (laurentMinus_projection P b)) ≪≫
      BoundedFlatPerfectBinarySimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((underToLaurentInvert R).app b) ≫ polynomialProjection P b))
    (middleIso P u v) i)

/-- The complete minus binary row is shared through its proved full central reference node. -/
theorem minus_middle_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassH1References.middleNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) :=
  prePost_families_match (commonReference P u v)
    (coefficientMapModel P u) (laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (minus_first_row P u v) (minus_middle_row P u v) 0 (first_middle_center P u v) i

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
