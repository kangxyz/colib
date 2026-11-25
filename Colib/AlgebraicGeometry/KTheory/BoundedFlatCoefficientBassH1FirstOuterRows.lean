/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1OldChartCenter
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNativeMergedRows

/-!
# The original first Bass H₁ outer rows and old chart columns

The two original binary families use different factorizations before and
after projection. Each equality retains the complete dependent nodes
through the already proved full shared center. Adapted from
`H1FirstOuterRows.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectNativeMergedRows
open BoundedFlatCoefficientBassH1References

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

private theorem reanchorNode_refl_apply
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W)
    (N : Σ G : V ⟶ W, F.hom.toFunctor ≅ G.hom.toFunctor) :
    ModelSimplex.reanchorNode (F₀ := F) (F₁ := F) (Iso.refl _) N = N := by
  rcases N with ⟨G, e⟩
  exact congrArg (fun η : F.hom.toFunctor ≅ G.hom.toFunctor ↦
    (⟨G, η⟩ : Σ H : V ⟶ W, F.hom.toFunctor ≅ H.hom.toFunctor)) (Iso.refl_trans e)

-- Discharge the trivial reference transport before whiskering, without unfolding the chart
-- nodes in either specialized outer-row proof.
private theorem projectionNativeNode_eq_chartNodes (j : Fin 18) :
    projectionNativeNode (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (polynomialProjection_naturality P u)
      (coefficientMap_naturality_of_natTrans P α u)
      (laurentProjection P a) ha (BoundedFlatCoefficientBassH0Diagram.reference P u) rfl j =
    BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha j :=
  reanchorNode_refl_apply (BoundedFlatCoefficientBassH0Diagram.reference P u)
    (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha j)

/-- The binary source combining the Laurent map along `u` with the chart coefficient map at `a`. -/
abbrev outerFirstSource := BoundedFlatPerfectBinarySimplex.sourceMap
  (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
/-- The three binary normalization nodes for the Laurent map along `u` and the chart map at `a`. -/
abbrev outerFirstBinary := binaryNodes
  (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
/--
The binary source combining the chart coefficient map at `b` with the polynomial map along `u`.
-/
abbrev outerSecondSource := BoundedFlatPerfectBinarySimplex.sourceMap
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))
/--
The three binary normalization nodes for the chart map at `b` and the polynomial map along `u`.
-/
abbrev outerSecondBinary := binaryNodes
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The first row representation is constructed from the original projection reference. -/
theorem first_outer_first_representation : ∃ ρ, ∀ i : Fin 3,
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    prePostNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v) (outerFirstSource P u α)
        (outerFirstBinary P u α) ρ i := by
  refine ⟨firstIso P u v ≪≫ isoWhiskerRight
    (rightRowReference (BoundedFlatCoefficientBassH0Diagram.reference P u)
      (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
      (polynomialProjection P a)
      (projectionFirstReference (polynomialProjection P a) (coefficientMap P (α.app a))
        (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a) ha
        (BoundedFlatCoefficientBassH0Diagram.reference P u) rfl))
    (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor, ?_⟩
  intro i
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (projection_first_right_row (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (polynomialProjection_naturality P u)
      (coefficientMap_naturality_of_natTrans P α u)
        (laurentProjection P a) ha (BoundedFlatCoefficientBassH0Diagram.reference P u) rfl i)
  have hchart := congrArg (postReferenceNode
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (projectionNativeNode_eq_chartNodes P u α ha
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))).symm
  refine hchart.trans (hn.trans ?_)
  exact post_pre_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) _ (firstIso P u v) i

/-- The second row representation retains the actual middle-square source transport. -/
theorem first_outer_second_representation : ∃ ρ, ∀ i : Fin 3,
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    prePostNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v) (outerSecondSource P u α)
      (outerSecondBinary P u α) ρ i := by
  refine ⟨firstIso P u v ≪≫ isoWhiskerRight
    (rightRowReference (BoundedFlatCoefficientBassH0Diagram.reference P u)
      (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a) (projectionMiddleReference (polynomialProjection P a)
        (coefficientMap P (α.app a))
        (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))
        (coefficientMap P ((laurentUnderFunctor R).map u))
          (coefficientMap_naturality_of_natTrans P α u)
        (laurentProjection P a) ha (BoundedFlatCoefficientBassH0Diagram.reference P u) rfl))
    (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor, ?_⟩
  intro i
  have hn := congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (projection_middle_right_row (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (polynomialProjection_naturality P u)
      (coefficientMap_naturality_of_natTrans P α u)
        (laurentProjection P a) ha (BoundedFlatCoefficientBassH0Diagram.reference P u) rfl i)
  have hchart := congrArg (postReferenceNode
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
    (projectionNativeNode_eq_chartNodes P u α ha
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))).symm
  refine hchart.trans (hn.trans ?_)
  exact post_pre_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) _ (firstIso P u v) i

/--
The last-source isomorphism for the two chart naturality squares along `u` and `v`, before
projection precomposition.
-/
abbrev oldLastTripleReference := BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientMap_naturality_of_natTrans P α u).symm
  (coefficientMap_naturality_of_natTrans P α v).symm

/--
The middle-source isomorphism for the chart naturality square along `v`, with the polynomial map
along `u` retained.
-/
abbrev oldMiddleTripleReference := BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientMap_naturality_of_natTrans P α v).symm

/-- The old last column uses the original geometric total-square reference before precomposition. -/
theorem old_outer_last_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    prePostNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v) (outerFirstSource P u α)
        (outerFirstBinary P u α) ρ i := by
  refine ⟨BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a)).hom.toFunctor
      (oldLastTripleReference P u v α ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))), ?_⟩
  intro i
  have hn := congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc))
    (merged_last_column
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientMap_naturality_of_natTrans P α u).symm
      (coefficientMap_naturality_of_natTrans P α v).symm i)
  exact hn.trans (pre_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) _
    (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc) i)

/-- The old middle column retains the original v-square source transport before precomposition. -/
theorem old_outer_middle_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    prePostNodes (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v) (outerSecondSource P u α)
      (outerSecondBinary P u α) ρ i := by
  refine ⟨BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a)).hom.toFunctor
      (oldMiddleTripleReference P u v α ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))), ?_⟩
  intro i
  have hn := congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc))
    (merged_middle_column
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientMap_naturality_of_natTrans P α u).symm
      (coefficientMap_naturality_of_natTrans P α v).symm i)
  exact hn.trans (pre_post_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) _
    (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc) i)

/-- The entire first original u-square binary row agrees with the old last column. -/
theorem first_old_outer_first_nodes (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) := by
  obtain ⟨ρ, hρ⟩ := first_outer_first_representation P u v α ha
  obtain ⟨σ, hσ⟩ := old_outer_last_representation P u v α hc
  exact prePost_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) hρ hσ
    0 (first_old_chart_center P u v α ha hc) i

/-- The entire other original u-square row agrees through the same full shared source. -/
theorem first_old_outer_second_nodes (i : Fin 3) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) := by
  obtain ⟨ρ, hρ⟩ := first_outer_second_representation P u v α ha
  obtain ⟨σ, hσ⟩ := old_outer_middle_representation P u v α hc
  exact prePost_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) hρ hσ
    0 (first_old_chart_center P u v α ha hc) i

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
