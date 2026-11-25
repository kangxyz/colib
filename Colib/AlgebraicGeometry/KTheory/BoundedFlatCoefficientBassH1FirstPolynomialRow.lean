/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ProductColumnCenter

/-!
# The first polynomial row shared by the first H₁ face and chart product

The actual normalized polynomial row, with both fixed postcompositions,
is identified through the full common center. In particular its endpoint
is the same original dependent node as in the old chart. Adapted from
`ProjectionPolynomialColumns.lean` and `H1ProductPolynomialRows.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

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

/-- The original source anchor followed by the actual middle-square source transport. -/
def nativeMiddleReference : (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor ≅
    (BoundedFlatPerfectTripleSimplex.source q' b p).hom.toFunctor :=
  eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
    BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq

/-- The original projection middle column keeps its binary family and postcomposition anchor. -/
theorem native_middle_column (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (H := BoundedFlatPerfectBinarySimplex.sourceMap b p)
        (nativeMiddleReference p q q' b c hq r hr ≪≫ BoundedFlatPerfectBinarySimplex.total q'
          (b ≫ p))
        (binaryNodes b p i) := by
  let ρ := eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)
  have hn := reanchorNode_congr
    (F₀ := BoundedFlatPerfectProjectionReference.reference c r)
    (F₁ := BoundedFlatPerfectTripleSimplex.source c q p) ρ
    (merged_middle_column p q p' q' a b c hp hq i)
  refine hn.trans ?_
  unfold reanchorNode postReferenceNode nativeMiddleReference
  dsimp only
  simp only [ρ, Iso.trans_assoc]

end Projection

section Square

open BoundedFlatPerfectNativeSquareFiveSimplex

variable {X Y Z T U : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)
  (F : asSmallCategory (W Z) ⟶ asSmallCategory (W U))
  (J : asSmallCategory (W X) ⟶ asSmallCategory (W U))
  (ρ : F.hom.toFunctor ≅ (source p v ≫ J).hom.toFunctor)

/-- The original first square triangle after the actual fixed postcomposition. -/
theorem post_square_first_nodes (i : Fin 3) :
    postReferenceNode F J ρ (nodes p v q w h (firstFace.toOrderHom i)) =
      postReferenceNode F J ρ (binaryNodes p v i) := by
  apply congrArg (postReferenceNode F J ρ)
  fin_cases i <;> rfl

end Square

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/--
The normalized chart coefficient map at `b` followed by the Laurent coefficient map along `v`.
-/
abbrev polynomialJoinPost := normalizedMap (coefficientMap P (α.app b)) ≫
  BoundedFlatCoefficientBassH1Components.laurentMap P v

/--
The native middle-square reference for the chart naturality square along `u` and its projection
equality `ha`.
-/
abbrev polynomialMiddleReference := nativeMiddleReference
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap_naturality_of_natTrans P α u)
    (laurentProjection P a) ha

/--
The reference for the first polynomial row, with its middle-square transport postwhiskered by
the Laurent map along `v`.
-/
def firstPolynomialRowReference := firstIso P u v ≪≫ isoWhiskerRight
  (polynomialMiddleReference P u α ha ≪≫ BoundedFlatPerfectBinarySimplex.total
    (coefficientMap P (α.app b))
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))
  (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor

/--
The product-column reference obtained by prewhiskering the binary chart normalization by the
polynomial source.
-/
def productPolynomialReference := chartIso P u v α hb ≪≫
  isoWhiskerLeft (BoundedFlatCoefficientSquareFamilies.polynomialSource P u).hom.toFunctor
    (BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))

/-- The first component's first polynomial row is its original two normalizations postcomposed. -/
theorem first_polynomial_row (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (polynomialJoinPost P v α)
      (firstPolynomialRowReference P u v α ha)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (native_middle_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (polynomialProjection_naturality P u)
      (coefficientMap_naturality_of_natTrans P α u)
        (laurentProjection P a) ha i)
  exact hn.trans (post_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app b)))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (BoundedFlatCoefficientSquareFamilies.polynomialSource P u) _ (firstIso P u v) _)

/-- The product column is the original whole polynomial square after fixed postcomposition. -/
theorem product_polynomial_column (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4 (i, 2)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb)
        (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i) :=
  CommonReferenceProduct.product_column_nodes
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).2)
    (BoundedFlatCoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).2) (chartIso P u v α hb) i 2

/-- The first product-column row retains the first original polynomial binary reference. -/
theorem product_polynomial_first_row (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i, 2)) =
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) :=
  (product_polynomial_column P u v α hb _).trans (post_square_first_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (polynomialProjection_naturality P u)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (productPolynomialReference P u v α hb) i)

/-- The complete first binary row is fixed by the proved original central node identity. -/
theorem first_product_polynomial_first_nodes (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) =
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i, 2)) :=
  post_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (polynomialJoinPost P v α)
    (BoundedFlatCoefficientSquareFamilies.polynomialSource P u)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a))
    (first_polynomial_row P u v α ha) (product_polynomial_first_row P u v α hb)
    0 (first_product_polynomial_center P u v α ha hb) i

variable
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

include ha in
/-- The shared first-row endpoint is the original old-chart node, including its reference iso. -/
theorem product_old_outer_endpoint :
    chartNodes P u v α hb 12 = BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc 13 :=
  (first_product_polynomial_first_nodes P u v α ha hb 2).symm.trans
    (first_old_outer_second_nodes P u v α ha hc 2)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
