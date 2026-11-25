/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1SecondPolynomialRow

/-!
# Original signed centers of the middle H₁ face and product rows

The original first normalized projection node and the actual product row
source coincide as full dependent nodes. The inverse coordinate case keeps
its own projection equality. Adapted from `ProjectionFirstNormalNode.lean`
and `H1ProductRowCenter.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Topology
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

include hr in
/-- The actual projection equation, with the original right association retained. -/
theorem projection_first_geom : c ≫ r = (c ≫ q) ≫ p := by
  rw [Category.assoc, hr]

include hr in
theorem projection_first_source_eq :
    (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (c ≫ q) p).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (projection_first_geom p q c r hr))

theorem projection_first_normal_functor :
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 9).1.hom.toFunctor =
      (BoundedFlatPerfectBinarySimplex.targetMap (c ≫ q) p).hom.toFunctor := rfl

/-- The first normalized right-row reference retains its native associativity transport. -/
theorem projection_first_normal_reference :
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 9).2 =
      eqToIso (projection_first_source_eq p q c r hr) ≪≫
        BoundedFlatPerfectBinarySimplex.total (c ≫ q) p := by
  change eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (Category.assoc c q p).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (c ≫ q) p) = _
  rw [smallIso_trans, smallIso_eqToIso, ← Iso.trans_assoc, eqToIso_trans]; rfl

/-- Full original normalized right-row node, including the actual dependent reference. -/
theorem projection_first_normal :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 9 =
      (⟨BoundedFlatPerfectBinarySimplex.targetMap (c ≫ q) p,
        eqToIso (projection_first_source_eq p q c r hr) ≪≫
          BoundedFlatPerfectBinarySimplex.total
            (c ≫ q) p⟩ : BoundedFlatPerfectProjectionReference.Node c r) := by
  apply ModelSimplex.reference_node_eq
    (projection_first_normal_functor p q p' q' a b c hp hq r hr)
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg Iso.hom (projection_first_normal_reference p q p' q' a b c hp hq r hr)
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/--
The chart projection equality with the Laurent coefficient map composed with the chart map
before polynomial projection.
-/
abbrev chartFirstGeom := projection_first_geom (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map u))
  (laurentProjection P a) ha

/--
The source-functor equality for the first normalized chart row, induced by the chart projection
equality.
-/
abbrev chartFirstSourceEq := projection_first_source_eq (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map u))
  (laurentProjection P a) ha

/-- The whole original coefficient-chart node retains that same projection association. -/
theorem chart_first_normal : BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 9 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))
      (polynomialProjection P a),
      eqToIso (chartFirstSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))
        (polynomialProjection P a)⟩ : BoundedFlatCoefficientBassH0Diagram.Node P u) :=
  projection_first_normal (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (polynomialProjection_naturality P u)
    (coefficientMap_naturality_of_natTrans P α u)
      (laurentProjection P a) ha

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/--
The middle-component chart center, normalized through the polynomial projection at `b` and
precomposed by the coefficient map along `u`.
-/
def middleChartCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b),
      eqToIso (chartFirstSourceEq P v α hb) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)⟩ : BoundedFlatCoefficientBassH0Diagram.Node P v)

/--
The product-row center formed from the final polynomial-square node and the chart source, with
their common reference.
-/
def productChartCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  ⟨(BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).1 ≫
    BoundedFlatCoefficientSquareFamilies.chartSource P v α,
    chartIso P u v α hb ≪≫
      isoWhiskerRight (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).2
      (BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor⟩

theorem middle_chart_center_original :
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BoundedFlatCoefficientBassH0Diagram.chartNodes P v α hb 9) = middleChartCenter P u v α hb :=
  congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v))
      (chart_first_normal P v α hb)

/-- The product center retains its actual original polynomial-square target reference. -/
theorem product_chart_center_original :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb 20 =
      productChartCenter P u v α hb := by
  change BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4
    (4, 0)) = _
  unfold BoundedFlatCoefficientBassH1References.chartNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  have hf : ((BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).1 ≫
      (BoundedFlatCoefficientSquareFamilies.chartNodes P v α 0).1).hom.toFunctor =
      (productChartCenter P u v α hb).1.hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change chartIso P u v α hb ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).2.prod
        (Iso.refl (BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor)) = _
  have hi := CommonReferenceProduct.composition_pair_iso
    (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).2
    (Iso.refl (BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor)
  simp only [isoWhiskerLeft_refl, Iso.trans_refl] at hi
  exact congrArg (fun ν ↦ chartIso P u v α hb ≪≫ ν) hi

theorem chart_center_functor : (middleChartCenter P u v α hb).1.hom.toFunctor =
    (productChartCenter P u v α hb).1.hom.toFunctor := rfl

/-- The original row centers agree by canonical normalized three-factor associativity. -/
theorem chart_center_reference : (middleChartCenter P u v α hb).2 =
    (productChartCenter P u v α hb).2 := by
  have hm : eqToIso (chartFirstSourceEq P v α hb) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (chartFirstGeom P v α hb)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  have hp : (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).2 =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (polynomialProjection_naturality P u)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (polynomialProjection P b)
        (coefficientMap P u)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change middleIso P u v ≪≫
    isoWhiskerLeft (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u).hom.toFunctor
      (eqToIso (chartFirstSourceEq P v α hb) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)) =
    chartIso P u v α hb ≪≫
      isoWhiskerRight (BoundedFlatCoefficientSquareFamilies.polynomialNodes P u 4).2
      (BoundedFlatCoefficientSquareFamilies.chartSource P v α).hom.toFunctor
  rw [hm, hp]
  change smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
    (middle_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
        (coefficientMap P u)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
      (coefficientMap P u) ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (chartFirstGeom P v α hb)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso
          (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
          (polynomialProjection P b))) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (chart_total P u v α hb).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (polynomialProjection_naturality P u)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (polynomialProjection P b)
        (coefficientMap P u)))
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ⋙
          AsSmall.up)
  rw [smallIso_precomp, smallIso_postcomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b) (coefficientMap P u)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chartFirstGeom P v α hb)
      (polynomialProjection_naturality P u)
      (middle_total P u v).symm (chart_total P u v α hb).symm)

/-- Both original full central nodes agree, with every normalization and equality iso retained. -/
theorem middle_product_chart_center :
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BoundedFlatCoefficientBassH0Diagram.chartNodes P v α hb 9) =
        BoundedFlatCoefficientBassH1References.chartNodes P u v α hb 20 := by
  rw [middle_chart_center_original, product_chart_center_original]
  apply ModelSimplex.reference_node_eq (chart_center_functor P u v α hb)
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg Iso.hom (chart_center_reference P u v α hb)

theorem plus_row_center : BoundedFlatCoefficientBassH1References.middleNodes P u v 9 =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurent R)
      (laurentPlus_projection P b) 20 :=
  middle_product_chart_center P u v (underToLaurent R) (laurentPlus_projection P b)

theorem minus_row_center : BoundedFlatCoefficientBassH1References.middleNodes P u v 20 =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P b) 20 :=
  middle_product_chart_center P u v (underToLaurentInvert R) (laurentMinus_projection P b)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
