/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1BottomCenter
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoinFace
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# The shared source edge of the first Bass H₁ component and the Laurent bottom

The five dependent reference nodes are the original signed binary projection
rows along the last physical column of the Laurent grid. Adapted from
`H1BottomRows.lean` in Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex CommonReferenceProduct BoundedFlatCoefficientBassH1References
open BoundedFlatPerfectProjectionBinaryRows

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The composite Laurent coefficient map used to postcompose the bottom boundary nodes. -/
abbrev bottomJoinPost :=
  BoundedFlatCoefficientBassH1Components.laurentMap P u ≫
    BoundedFlatCoefficientBassH1Components.laurentMap P v

/--
Identifies the common reference with the first binary projection source after both Laurent maps,
using the source projection equality `ha`.
-/
def firstSourceRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :=
  firstIso P u v ≪≫ isoWhiskerRight
    (eqToIso (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.sourceAnchor P u α ha) ≪≫
      BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P (α.app a) ≫ polynomialProjection P a))
    (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor

/--
Identifies the common reference with the projection path at `a` postcomposed by both Laurent
coefficient maps.
-/
def bottomColumnReference := BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
  isoWhiskerLeft (BoundedFlatCoefficientBassProjectionPath.source P a).hom.toFunctor
    (BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)))

/-- The original positive projection row after both actual Laurent coefficient maps. -/
theorem first_source_plus_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (bottomJoinPost P u v)
      (H := BoundedFlatPerfectBinarySimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
      (firstSourceRowReference P u v (underToLaurent R) (laurentPlus_projection P a))
      (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.plus_source P u i)
  exact hn.trans (post_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P u)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    _ (firstIso P u v) _)

/-- The original inverse projection row retains its separate projection source equality. -/
theorem first_source_minus_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (bottomJoinPost P u v)
      (H := BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
      (firstSourceRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a))
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.minus_source P u i)
  exact hn.trans (post_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P u)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    _ (firstIso P u v) _)

/-- The bottom target column is the original Bass projection family after both Laurent maps. -/
theorem bottom_target_column (i : Fin 5) :
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v (SimplexGrid.index 4 2 (i, 2)) =
      postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (bottomJoinPost P u v)
        (bottomColumnReference P u v) (BoundedFlatCoefficientBassProjectionPath.nodes P a i) :=
  product_column_nodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassProjectionPath.source P a)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).1)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).2)
    (BoundedFlatCoefficientBassLaurentBottomFace.source P u v)
    (BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v)
    (BoundedFlatCoefficientBassLaurentBottomFace.references P u v)
    (BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v) i 2

section ProjectionRows

variable (a : Under R) {U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u + 1}}
  (F : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn (space (op P, a))) ⟶ U)
  (J : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn
    (space (op P, (laurentUnderFunctor R).obj a))) ⟶ U)
  (ρ : F.hom.toFunctor ≅ (BoundedFlatCoefficientBassProjectionPath.source P a ≫ J).hom.toFunctor)

private theorem post_projection_plus_nodes (i : Fin 3) :
    postReferenceNode F J ρ (BoundedFlatCoefficientBassProjectionPath.nodes P a
      (BoundedFlatCoefficientBassProjectionPath.plusFace.toOrderHom i)) =
    postReferenceNode F J ρ (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) := by
  fin_cases i <;> rfl

private theorem post_projection_minus_nodes (i : Fin 3) :
    postReferenceNode F J ρ (BoundedFlatCoefficientBassProjectionPath.nodes P a
      (BoundedFlatCoefficientBassProjectionPath.minusFace.toOrderHom i)) =
    postReferenceNode F J
      (ρ ≪≫ isoWhiskerRight
        (BoundedFlatCoefficientBassProjectionPath.sourceIso P a) J.hom.toFunctor)
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  have h (j : Fin 3) : BoundedFlatCoefficientBassProjectionPath.nodes P a
      (BoundedFlatCoefficientBassProjectionPath.minusFace.toOrderHom j) =
      BoundedFlatCoefficientBassProjectionPath.minusNodes P a j := by
    fin_cases j
    · apply ModelSimplex.reference_node_eq (BoundedFlatCoefficientBassProjectionPath.source_eq P a)
      simp [BoundedFlatCoefficientBassProjectionPath.minusReferences,
        BoundedFlatCoefficientBassProjectionPath.sourceIso]
    · rfl
    · rfl
  rw [h]
  fin_cases i <;>
    simp only [BoundedFlatCoefficientBassProjectionPath.minusNodes, postReferenceNode,
      isoWhiskerRight_trans, Iso.trans_assoc] <;> rfl

end ProjectionRows

/-- The positive bottom row retains the original two binary normalization transformations. -/
theorem bottom_target_plus_row (i : Fin 3) :
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
      (SimplexGrid.index 4 2 (BoundedFlatCoefficientBassProjectionPath.plusFace.toOrderHom i, 2)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (bottomJoinPost P u v)
      (bottomColumnReference P u v)
      (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) :=
  (bottom_target_column P u v _).trans (post_projection_plus_nodes P a
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (bottomJoinPost P u v)
    (bottomColumnReference P u v) i)

/-- The inverse bottom row includes the unchanged positive-to-inverse source equality. -/
theorem bottom_target_minus_row (i : Fin 3) :
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
      (SimplexGrid.index 4 2 (BoundedFlatCoefficientBassProjectionPath.minusFace.toOrderHom i, 2)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (bottomJoinPost P u v)
      (bottomColumnReference P u v ≪≫
        isoWhiskerRight (BoundedFlatCoefficientBassProjectionPath.sourceIso P a)
          (bottomJoinPost P u v).hom.toFunctor)
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) :=
  (bottom_target_column P u v _).trans (post_projection_minus_nodes P a
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (bottomJoinPost P u v)
    (bottomColumnReference P u v) i)

/-- Full positive source row shared by the original first H₁ cell and original bottom face. -/
theorem first_bottom_plus_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
      (SimplexGrid.index 4 2 (BoundedFlatCoefficientBassProjectionPath.plusFace.toOrderHom i, 2)) :=
  post_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (bottomJoinPost P u v)
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    (binaryNodes (laurentPlus P a) (polynomialProjection P a))
    (first_source_plus_row P u v) (bottom_target_plus_row P u v) 0 (first_bottom_center P u v) i

/-- The full inverse row uses the same proved central node and its actual native transports. -/
theorem first_bottom_minus_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
      (SimplexGrid.index 4 2
        (BoundedFlatCoefficientBassProjectionPath.minusFace.toOrderHom i, 2)) :=
  post_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (bottomJoinPost P u v)
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    (binaryNodes (laurentMinus P a) (polynomialProjection P a))
    (first_source_minus_row P u v) (bottom_target_minus_row P u v) 0 (first_bottom_center P u v) i

/-- Every dependent node on the entire external source edge is shared with the original bottom. -/
theorem first_bottom_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v (middleSourceFace.toOrderHom i) =
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
      (SimplexGrid.index 4 2 (i, 2)) := by
  fin_cases i
  · exact first_bottom_center P u v
  · exact first_bottom_plus_nodes P u v 1
  · exact first_bottom_plus_nodes P u v 2
  · exact first_bottom_minus_nodes P u v 1
  · exact first_bottom_minus_nodes P u v 2

/-- The actual first source and Laurent target column are the same complete four-simplex. -/
theorem first_bottom_face :
    (BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face middleSourceFace =
      (BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v).face
        (SimplexGrid.columnFace 4 2 2) := by
  rw [← BoundedFlatCoefficientBassH1References.first_original,
    ← BoundedFlatCoefficientBassBottomCommonFamily.bottom_reference,
    ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (first_bottom_nodes P u v)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
