/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1OuterScalarWords
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOldChartBinaryRows

/-!
# The common outer chart center of the first Bass H₁ face

Both signed first-component centers have the full original reference of
their old chart center. The proof keeps the normalization of both routes
and compares their actual geometric factorization isomorphisms.
Adapted from `ProjectionMiddleRightNormal.lean`, `OldChartMiddleNormal.lean`
and `H1OldChartCenter.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex BoundedFlatCoefficientBassH1References BoundedFlatPerfectReferenceCoherence

section Schemes
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

include hq hr in
/-- The actual square and projection equations give the middle-right normalized total. -/
theorem projection_middle_right_geom : c ≫ r = (q' ≫ b) ≫ p :=
  (congrArg (fun k ↦ c ≫ k) hr.symm).trans
    ((BoundedFlatPerfectDoubleSquareCommonSimplex.middle_eq p q q' b c hq).symm.trans
      (Category.assoc q' b p).symm)

include hq hr in
theorem projection_middle_right_source_eq :
    (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (q' ≫ b) p).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback
      (projection_middle_right_geom p q q' b c hq r hr))

/-- The shared original node is exactly its middle-triple normalized factorization. -/
theorem projection_middle_right_normal :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 9 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap (q' ≫ b) p,
      eqToIso (projection_middle_right_source_eq p q q' b c hq r hr) ≪≫
        BoundedFlatPerfectBinarySimplex.total
          (q' ≫ b) p⟩ : BoundedFlatPerfectProjectionReference.Node c r) := by
  have hn := BoundedFlatPerfectProjectionBinaryRows.projection_middle_nodes
    p q p' q' a b c hp hq r hr (BoundedFlatPerfectProjectionReference.reference c r) rfl 5
  have hn' :
      BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 9 =
        (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p 5,
          (eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
            BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) ≪≫
              BoundedFlatPerfectSplitTripleSimplex.references q' b p 5⟩ :
          BoundedFlatPerfectProjectionReference.Node c r) := by
    have hindex : BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom 5 = 9 :=
      by decide
    rw [hindex] at hn
    simpa only [BoundedFlatPerfectProjectionBinaryRows.projectionNativeNode,
      BoundedFlatPerfectProjectionBinaryRows.projectionMiddleReference,
      BoundedFlatPerfectProjectionBinaryRows.projectionFirstReference, ModelSimplex.reanchorNodes,
      ModelSimplex.reanchorNode, eqToIso_refl, Iso.refl_trans] using hn
  refine hn'.trans ?_
  have hf : (BoundedFlatPerfectSplitTripleSimplex.vertices q' b p 5).hom.toFunctor =
      (BoundedFlatPerfectBinarySimplex.targetMap (q' ≫ b) p).hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  change Iso.hom ((eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
      smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_eq p q q' b c hq).symm))) ≪≫
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (Category.assoc q' b p).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (q' ≫ b) p)) = _
  rw [smallIso_trans, smallIso_eqToIso, smallIso_eqToIso,
    ← Iso.trans_assoc, eqToIso_trans, eqToIso_trans]; rfl
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/--
The chart projection equality with the chart map and polynomial coefficient map composed before
polynomial projection.
-/
abbrev chartMiddleRightGeom := projection_middle_right_geom
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap_naturality_of_natTrans P α u)
    (laurentProjection P a) ha

/--
The source-functor equality for the middle-right chart node, with the first two geometric maps
composed before normalization.
-/
abbrev chartMiddleRightSourceEq := projection_middle_right_source_eq
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap_naturality_of_natTrans P α u)
    (laurentProjection P a) ha

/-- The original coefficient node retains the full actual middle-square reference route. -/
theorem chart_middle_right_normal : BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 9 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a),
      eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)⟩ : BoundedFlatCoefficientBassH0Diagram.Node P u) :=
  projection_middle_right_normal (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (polynomialProjection_naturality P u)
    (coefficientMap_naturality_of_natTrans P α u)
      (laurentProjection P a) ha

section Schemes
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/--
The middle-square geometric equality oriented from the common triple composite to the binary
middle composite.
-/
abbrev mergedMiddleGeom :=
  (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_eq p q q' b c hq).symm

include hq in
theorem mergedMiddleSourceEq : (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap q' (b ≫ p)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (mergedMiddleGeom p q q' b c hq))

/-- The full actual middle node retains its original source-square equality and normalization. -/
theorem merged_middle_normal :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 5 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap q' (b ≫ p),
      eqToIso (mergedMiddleSourceEq p q q' b c hq) ≪≫
        BoundedFlatPerfectBinarySimplex.total q' (b ≫ p)⟩ :
      BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) := by
  have hf : (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
    5).1.hom.toFunctor =
      (BoundedFlatPerfectBinarySimplex.targetMap q' (b ≫ p)).hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  change Iso.hom (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_eq p q q' b c hq).symm)) ≪≫
      smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso q' (b ≫ p))) = _
  rw [smallIso_eqToIso]; rfl
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/--
The middle-square geometric equality specialized to the polynomial-to-Laurent coefficient chart.
-/
abbrev oldChartMiddleGeom := mergedMiddleGeom
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientMap_naturality_of_natTrans P α v).symm

/--
The source-functor equality for the chart's middle node, induced by the specialized
middle-square equality.
-/
abbrev oldChartMiddleSourceEq := mergedMiddleSourceEq
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientMap_naturality_of_natTrans P α v).symm

/-- The original chart's whole dependent middle node has this exact normalized representation. -/
theorem old_chart_middle_normal : BoundedFlatCoefficientBassOverlap.chartNodes P u v α 5 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)),
      eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))⟩ :
      BoundedFlatPerfectDoubleSquareCommonSimplex.Node
        (coefficientMap P ((polynomialUnderFunctor R).map u))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) (coefficientMap P (α.app c))) :=
  merged_middle_normal
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α u).symm
    (coefficientMap_naturality_of_natTrans P α v).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/--
The first-component outer chart center, normalized at the polynomial projection and postcomposed
by the Laurent map along `v`.
-/
def firstOuterCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a),
      eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)⟩ : BoundedFlatCoefficientBassH0Diagram.Node P u)

/--
The old outer chart center, normalized at the Laurent map along `v` and precomposed by the
projection at `a`.
-/
def oldOuterCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)),
      eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))⟩ :
      Σ G, (BoundedFlatCoefficientBassOverlap.chartReference P u v α).hom.toFunctor ≅
        G.hom.toFunctor)

theorem first_outer_center_original :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 9) =
        firstOuterCenter P u v α ha :=
  congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
      (chart_middle_right_normal P u α ha)

theorem old_outer_center_original :
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc 5 =
    oldOuterCenter P u v α hc :=
  congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc))
    (old_chart_middle_normal P u v α)

theorem outer_center_functor : (firstOuterCenter P u v α ha).1.hom.toFunctor =
    (oldOuterCenter P u v α hc).1.hom.toFunctor := rfl

/-- All original chart, projection and composition equality transports agree canonically. -/
theorem outer_center_reference : (firstOuterCenter P u v α ha).2 =
    (oldOuterCenter P u v α hc).2 := by
  have hfirst : eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (chartMiddleRightGeom P u α ha)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  have hold : eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (oldChartMiddleGeom P u v α)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (coefficientMap P
        ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a))
          (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor =
    BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a)).hom.toFunctor
        (eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BoundedFlatPerfectBinarySimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)))
  rw [hfirst, hold]
  change smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
    (first_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (coefficientMap P
        ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (chartMiddleRightGeom P u α ha)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
          (polynomialProjection P a)))
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (BoundedFlatCoefficientBassOverlap.chart_total P u v α hc).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
      (polynomialProjection P a) ⋙
      AsSmall.up)
      (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (oldChartMiddleGeom P u v α)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso (coefficientMap P
          ((laurentUnderFunctor R).map v))
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    (anchored_factorizations_strict (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a)
      (coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (oldChartMiddleGeom P u v α) (chartMiddleRightGeom P u α ha)
      (BoundedFlatCoefficientBassOverlap.chart_total P u v α hc).symm (first_total P u v).symm).symm

/-- The actual full outer center is shared with the unchanged old composition chart. -/
theorem first_old_chart_center :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 9) =
      BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc 5 := by
  rw [first_outer_center_original, old_outer_center_original]
  apply ModelSimplex.reference_node_eq (outer_center_functor P u v α ha hc)
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg Iso.hom (outer_center_reference P u v α ha hc)

/-- Full positive first-cell/chart center in the fixed old44 family. -/
theorem first_old_plus_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 9 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 5 :=
  (first_old_chart_center P u v (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P c)).trans
    (BoundedFlatCoefficientBassOldChartBinaryRows.old_plus_node P u v 5).symm

/-- Full inverse first-cell/chart center, with its distinct inverse-coordinate reference. -/
theorem first_old_minus_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 20 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 29 :=
  (first_old_chart_center P u v (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P c)).trans
    (BoundedFlatCoefficientBassOldChartBinaryRows.old_minus_node P u v 5).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
