/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ProductOuterJoins

/-!
# The complete signed polynomial columns and old bottom nodes

The second binary comparison retains its actual last-square reference.
Together with the first binary comparison this identifies all five nodes
in each original signed first/product column. The first/old62 bottom
column also retains its exact five full nodes. Adapted from
`ProjectionPolynomialColumns.lean`, `H1ProductPolynomialRows.lean`,
`H1InternalNodeJoins.lean`, and `H1BottomRows.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectNativeMergedRows
open BoundedFlatCoefficientBassH1References

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

section Projection

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- The whole native last projection column retains its actual square-induced reference. -/
theorem native_last_column (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (H := BoundedFlatPerfectBinarySimplex.sourceMap p' a)
        (nativeLastReference p q p' q' a b c hp hq r hr ≪≫ BoundedFlatPerfectBinarySimplex.total q'
          (p' ≫ a))
        (binaryNodes p' a i) := by
  let ρ := eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)
  have hn := reanchorNode_congr
    (F₀ := BoundedFlatPerfectProjectionReference.reference c r)
    (F₁ := BoundedFlatPerfectTripleSimplex.source c q p) ρ
    (merged_last_column p q p' q' a b c hp hq i)
  refine hn.trans ?_
  unfold reanchorNode postReferenceNode nativeLastReference
  dsimp only
  simp only [ρ, Iso.trans_assoc]

end Projection

private theorem post_reanchor_square_node
    {V M T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (F : V ⟶ T) (J : M ⟶ T) {H L : V ⟶ M}
    (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (η : H.hom.toFunctor ≅ L.hom.toFunctor) (D : CommonReferenceNerve.Node L) :
    postReferenceNode F J ρ (reanchorNode η D) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight η J.hom.toFunctor) D := by
  rcases D with ⟨G, σ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (G ≫ J).hom.toFunctor ↦
    (⟨G ≫ J, ν⟩ : CommonReferenceNerve.Node F))
  change ρ ≪≫ isoWhiskerRight (η ≪≫ σ) J.hom.toFunctor = _
  rw [isoWhiskerRight_trans, Iso.trans_assoc]

section Square

open BoundedFlatPerfectNativeSquareFiveSimplex

variable {X Y Z T U : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)
  (F : asSmallCategory (W Z) ⟶ asSmallCategory (W U))
  (J : asSmallCategory (W X) ⟶ asSmallCategory (W U))
  (ρ : F.hom.toFunctor ≅ (source p v ≫ J).hom.toFunctor)

private theorem post_square_second_reference (i : Fin 3) :
    nodes p v q w h (secondFace.toOrderHom i) =
      reanchorNode (sourceIso p v q w h) (binaryNodes q w i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq p v q w h)
    simp only [Iso.refl_hom, Category.id_comp, Fin.zero_eta, Fin.isValue, Iso.trans_hom]
    exact (Category.comp_id _).symm
  · rfl
  · rfl

/-- The second square triangle retains its geometric comparison under postcomposition. -/
theorem post_square_second_nodes (i : Fin 3) :
    postReferenceNode F J ρ (nodes p v q w h (secondFace.toOrderHom i)) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight (sourceIso p v q w h) J.hom.toFunctor)
        (binaryNodes q w i) := by
  refine (congrArg (postReferenceNode F J ρ) (post_square_second_reference p v q w h i)).trans ?_
  exact post_reanchor_square_node F J ρ (sourceIso p v q w h) (binaryNodes q w i)

end Square

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/--
The reference for the second polynomial row, with its last-triple transport postwhiskered by the
Laurent map along `v`.
-/
def secondPolynomialRowReference := firstIso P u v ≪≫ isoWhiskerRight
  (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.lastReference P u α ha ≪≫
    BoundedFlatPerfectBinarySimplex.total
    (coefficientMap P (α.app b)) (polynomialProjection P b ≫ coefficientMap P u))
  (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor

/-- The other polynomial row retains the native last-triple equality transport. -/
theorem second_polynomial_row (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (polynomialJoinPost P v α)
      (secondPolynomialRowReference P u v α ha)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) := by
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (native_last_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (polynomialProjection_naturality P u)
      (coefficientMap_naturality_of_natTrans P α u)
        (laurentProjection P a) ha i)
  exact hn.trans (post_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app b)))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (BoundedFlatPerfectBinarySimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    _ (firstIso P u v) _)

/-- The second product-column row retains the actual polynomial naturality source equality. -/
theorem product_polynomial_second_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i, 2)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb ≪≫ isoWhiskerRight
        (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso
          (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
          (polynomialProjection P b) (coefficientMap P u)
          (polynomialProjection_naturality P u))
        (polynomialJoinPost P v α).hom.toFunctor)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) :=
  (product_polynomial_column P u v α hb _).trans (post_square_second_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (polynomialProjection_naturality P u)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (productPolynomialReference P u v α hb) i)

/-- The complete second binary row retains the full source identity and source transport. -/
theorem first_product_polynomial_second_nodes (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) =
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i, 2)) :=
  post_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (polynomialJoinPost P v α)
    (BoundedFlatPerfectBinarySimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    (binaryNodes (polynomialProjection P b) (coefficientMap P u))
    (second_polynomial_row P u v α ha) (product_polynomial_second_row P u v α hb)
    0 (first_product_polynomial_center P u v α ha hb) i

/-- Original five-node word along the polynomial comparison. -/
def polynomialWordIndex : Fin 5 → Fin 18 := ![5, 6, 13, 7, 17]

/-- Every full polynomial-path node agrees with the actual product column. -/
theorem first_product_polynomial_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (i : Fin 5) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v)
      (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha (polynomialWordIndex i)) =
      BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4
        (i, 2)) := by
  fin_cases i
  · exact first_product_polynomial_first_nodes P u v α ha hb 0
  · exact first_product_polynomial_first_nodes P u v α ha hb 1
  · exact first_product_polynomial_first_nodes P u v α ha hb 2
  · exact first_product_polynomial_second_nodes P u v α ha hb 1
  · exact first_product_polynomial_second_nodes P u v α ha hb 2

/-- The complete positive first/product seam retains all five original dependent nodes. -/
theorem plus_column_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)) =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurent R)
      (laurentPlus_projection P b)
      (SimplexGrid.index 4 4 (i, 2)) := by
  exact (congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v))
    (BoundedFlatCoefficientBassH0Diagram.plus_nodes P u (polynomialWordIndex i))).trans
    (first_product_polynomial_nodes P u v (underToLaurent R)
      (laurentPlus_projection P a) (laurentPlus_projection P b) i)

/-- The distinct inverse first/product seam retains its actual inverse-chart references. -/
theorem minus_column_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i)) =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P b)
      (SimplexGrid.index 4 4 (i, 2)) := by
  exact (congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v))
    (BoundedFlatCoefficientBassH0Diagram.minus_nodes P u (polynomialWordIndex i))).trans
    (first_product_polynomial_nodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P a) (laurentMinus_projection P b) i)

/-- All five first-source references are the native old62 terminal-column nodes. -/
theorem first_old62_bottom_nodes (i : Fin 5) :
    firstNodes P u v (middleSourceFace.toOrderHom i) =
      BoundedFlatCoefficientBassH0Merged.nodes P u v (oldBottomEdgeFace.toOrderHom i) := by
  let j := SimplexGrid.index 4 2 (i, (2 : Fin 3))
  have h : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
      (BoundedFlatCoefficientBassBottomCommonFamily.bottomFace.toOrderHom j) =
      BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v j := by
    change BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v (Fin.natAdd 36 j) = _
    unfold BoundedFlatCoefficientBassBottomCommonFamily.nodes
    rw [Fin.addCases_right]
  exact (first_bottom_nodes P u v i).trans (h.symm.trans
    ((BoundedFlatCoefficientBassReferenceMerge.bottom_nodes P u v j).symm.trans
      (BoundedFlatCoefficientBassH0Merged.old_nodes P u v
        (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom j)).symm))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
