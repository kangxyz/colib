/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1FirstOuterJoins
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerve
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# The two binary rows of the chart product's outer H₁ edge

Fixing the polynomial square at its first normalized endpoint retains the
original chart family and its complete composite reference. Both binary
pieces of that exact row are displayed; equality with the old chart needs
a separate identification of the internal polynomial endpoint. Adapted
from `H1ProductOuterRows.lean`, `ProductReferenceRows.lean`, and
`ProjectionChartRows.lean` at Quillen commit
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

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1References

open BoundedFlatCoefficientBassOverlap (commonReference)
open BoundedFlatCoefficientSquareFamilies (polynomialSource polynomialNodes chartSource)
open BoundedFlatPerfectReferenceCoherence (smallIso)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The original product total uses the chart projection equation at the middle ring. -/
theorem chart_total
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ≫
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) =
        laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  calc
    _ = (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ≫
          (polynomialProjection P b ≫ coefficientMap P u) :=
      congrArg (fun k ↦
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ≫ k)
        (polynomialProjection_naturality P u)
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (coefficientMap P (α.app b)) (polynomialProjection P b), hb,
        ← Category.assoc (coefficientMap P ((laurentUnderFunctor R).map v))
          (laurentProjection P b)]
      exact middle_total P u v

/-- The common Laurent reference to the literal composite of the two square sources. -/
def chartIso
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (commonReference P u v).hom.toFunctor ≅
      (polynomialSource P u ≫ chartSource P v α).hom.toFunctor :=
  smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
    (chart_total P u v α hb).symm) ≪≫
    boundedAboveFlatPerfectNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))

/-- The chart product's full dependent nodes, anchored to the common Laurent reference. -/
def chartNodes
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (i : Fin 25) : CommonReferenceNerve.Node (commonReference P u v) :=
  ⟨CommonReferenceProduct.vertices
      (fun j ↦ (polynomialNodes P u j).1)
      (fun j ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α j).1) i,
    chartIso P u v α hb ≪≫ CommonReferenceProduct.references
      (polynomialSource P u)
      (fun j ↦ (polynomialNodes P u j).1) (fun j ↦ (polynomialNodes P u j).2)
      (chartSource P v α)
      (fun j ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α j).1)
      (fun j ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α j).2) i⟩

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1References

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows
open BoundedFlatCoefficientBassH1References

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

private theorem pre_reanchor_square_node
    {V M T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (F : V ⟶ T) (P : V ⟶ M) {H L : M ⟶ T}
    (ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor)
    (η : H.hom.toFunctor ≅ L.hom.toFunctor) (D : CommonReferenceNerve.Node L) :
    preReferenceNode F P ρ (reanchorNode η D) =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor η) D := by
  rcases D with ⟨G, σ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (P ≫ G).hom.toFunctor ↦
    (⟨P ≫ G, ν⟩ : CommonReferenceNerve.Node F))
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (η ≪≫ σ) = _
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

section Square

open BoundedFlatPerfectNativeSquareFiveSimplex

variable {X Y Z T U : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)
  (F : asSmallCategory (W U) ⟶ asSmallCategory (W X))
  (P : asSmallCategory (W U) ⟶ asSmallCategory (W Z))
  (ρ : F.hom.toFunctor ≅ (P ≫ source p v).hom.toFunctor)

/-- The original first triangle after the actual fixed precomposition. -/
theorem pre_square_first_nodes (i : Fin 3) :
    preReferenceNode F P ρ (nodes p v q w h (firstFace.toOrderHom i)) =
      preReferenceNode F P ρ (binaryNodes p v i) := by
  apply congrArg (preReferenceNode F P ρ)
  fin_cases i <;> rfl

private theorem square_second_reference (i : Fin 3) :
    nodes p v q w h (secondFace.toOrderHom i) =
      reanchorNode (sourceIso p v q w h) (binaryNodes q w i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq p v q w h)
    simp only [Iso.refl_hom, Category.id_comp, Fin.zero_eta, Fin.isValue, Iso.trans_hom]
    exact (Category.comp_id _).symm
  · rfl
  · rfl

/-- The other triangle keeps the square-induced equality when precomposed. -/
theorem pre_square_second_nodes (i : Fin 3) :
    preReferenceNode F P ρ (nodes p v q w h (secondFace.toOrderHom i)) =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (sourceIso p v q w h))
        (binaryNodes q w i) := by
  refine (congrArg (preReferenceNode F P ρ) (square_second_reference p v q w h i)).trans ?_
  exact pre_reanchor_square_node F P ρ (sourceIso p v q w h) (binaryNodes q w i)

end Square

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/-- Projection followed by the fixed normalized polynomial map along `u`. -/
abbrev outerProductPre := BoundedFlatCoefficientBassOverlap.projectionMap P (a := a) ≫
  normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The full product reference at polynomial normalization vertex 2. -/
def outerProductReference
    (hproj : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor ≅
      (outerProductPre P u ≫
        BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor :=
  chartIso P u v α hproj ≪≫
    isoWhiskerRight (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 2).2
      (BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor

/-- The entire actual row at the first normalized polynomial vertex. -/
theorem product_outer_row (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4 (2, i)) =
      preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (outerProductPre P u)
        (outerProductReference P u v α hb)
          (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i) :=
  CommonReferenceProduct.product_row_nodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u i).2)
    (BoundedFlatCoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (BoundedFlatCoefficientSquareFamilies.chartNodes P v α i).2) (chartIso P u v α hb) 2 i

/-- The first actual binary piece in the product's outer row. -/
theorem product_outer_first_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (2, BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) =
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) := by
  refine ⟨outerProductReference P u v α hb, fun i ↦ ?_⟩
  exact (product_outer_row P u v α hb _).trans (pre_square_first_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap_naturality_of_natTrans P α v)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (outerProductPre P u) _ i)

/-- The other actual binary piece, with the original chart equality transport. -/
theorem product_outer_second_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (2, BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) := by
  refine ⟨outerProductReference P u v α hb ≪≫ isoWhiskerLeft (outerProductPre P u).hom.toFunctor
    (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
      (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap_naturality_of_natTrans P α v)), fun i ↦ ?_⟩
  exact (product_outer_row P u v α hb _).trans (pre_square_second_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap_naturality_of_natTrans P α v)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (outerProductPre P u) _ i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
