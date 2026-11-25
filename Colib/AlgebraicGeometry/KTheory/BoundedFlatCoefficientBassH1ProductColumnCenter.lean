/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ProductOuterRows

/-!
# Common centers of the original first H₁ face and product column

The original projection middle node and the product column's normalized
center have the same full dependent reference. The positive and inverse
coordinate charts use their distinct actual projection identities. Adapted
from `ProjectionMiddleNormalNode.lean` and `H1ProductColumnCenter.lean` in
Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
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

include hq hr in
/-- The original square and projection equations give the exact middle total. -/
theorem projection_middle_geom : c ≫ r = q' ≫ b ≫ p := by
  calc
    _ = c ≫ q ≫ p := congrArg (fun k ↦ c ≫ k) hr.symm
    _ = _ := by rw [← Category.assoc, hq, Category.assoc]

include hq hr in
theorem projection_middle_source_eq :
    (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap q' (b ≫ p)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (projection_middle_geom p q q' b c hq r hr))

theorem projection_middle_normal_functor :
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 5).1.hom.toFunctor =
      (BoundedFlatPerfectBinarySimplex.targetMap q' (b ≫ p)).hom.toFunctor := rfl

/-- The actual middle reference is its unchanged native source transport and normalization. -/
theorem projection_middle_normal_reference :
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 5).2 =
      eqToIso (projection_middle_source_eq p q q' b c hq r hr) ≪≫
        BoundedFlatPerfectBinarySimplex.total q' (b ≫ p) := by
  change eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
    (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_eq p q q' b c hq).symm)) ≪≫
      smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso q' (b ≫ p))) = _
  rw [smallIso_eqToIso, ← Iso.trans_assoc, eqToIso_trans]; rfl

/-- Full dependent middle node, not merely its normalized endpoint functor. -/
theorem projection_middle_normal :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr 5 =
      (⟨BoundedFlatPerfectBinarySimplex.targetMap q' (b ≫ p),
        eqToIso (projection_middle_source_eq p q q' b c hq r hr) ≪≫
          BoundedFlatPerfectBinarySimplex.total q'
            (b ≫ p)⟩ : BoundedFlatPerfectProjectionReference.Node c r) := by
  apply ModelSimplex.reference_node_eq
    (projection_middle_normal_functor p q p' q' a b c hp hq r hr)
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg Iso.hom (projection_middle_normal_reference p q p' q' a b c hp hq r hr)
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/--
The source-functor equality for the middle chart node, using coefficient naturality and the
projection equation `ha`.
-/
abbrev chartMiddleSourceEq := projection_middle_source_eq
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap_naturality_of_natTrans P α u)
    (laurentProjection P a) ha

/-- The full actual coefficient-chart middle node retains that same geometric normalization. -/
theorem chart_middle_normal : BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 5 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a),
      eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P u) :=
  projection_middle_normal
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P u) (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (polynomialProjection_naturality P u)
    (coefficientMap_naturality_of_natTrans P α u)
      (laurentProjection P a) ha



variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/--
Rewrites the Laurent projection composite along `u` through the chart map at `b` and the
polynomial projection at `a`.
-/
abbrev chartMiddleGeom := projection_middle_geom
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap_naturality_of_natTrans P α u)
    (laurentProjection P a) ha

/--
The first-component polynomial center, with the middle-square source transport and Laurent
postcomposition.
-/
def firstPolynomialCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a),
      eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P u)

/--
The product-column center obtained by precomposing the normalized chart target node with the
polynomial source along `u`.
-/
def productPolynomialCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientSquareFamilies.polynomialSource P u) (chartIso P u v α hb)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)),
      BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))⟩ :
      BoundedFlatPerfectNativeSquareFiveSimplex.Node
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))

theorem first_polynomial_center_original :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 5) =
      firstPolynomialCenter P u v α ha :=
  congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v) (firstIso P u v))
      (chart_middle_normal P u α ha)

/-- The product's original source/normalized vertex has this exact complete reference. -/
theorem product_polynomial_center_original :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb 2 =
      productPolynomialCenter P u v α hb := by
  change BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4
    (0, 2)) = _
  unfold BoundedFlatCoefficientBassH1References.chartNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  have hf : (BoundedFlatCoefficientSquareFamilies.polynomialSource P u ≫
      BoundedFlatPerfectBinarySimplex.targetMap
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P
          (α.app b))).hom.toFunctor =
      (productPolynomialCenter P u v α hb).1.hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change chartIso P u v α hb ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (BoundedFlatCoefficientSquareFamilies.polynomialSource P u).hom.toFunctor).prod
        (BoundedFlatPerfectBinarySimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))) =
    chartIso P u v α hb ≪≫
      isoWhiskerLeft (BoundedFlatCoefficientSquareFamilies.polynomialSource P u).hom.toFunctor
        (BoundedFlatPerfectBinarySimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  have hi := CommonReferenceProduct.composition_pair_iso
    (Iso.refl (BoundedFlatCoefficientSquareFamilies.polynomialSource P u).hom.toFunctor)
    (BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  simp only [isoWhiskerRight_refl, Iso.refl_trans] at hi
  exact congrArg (fun ν ↦ chartIso P u v α hb ≪≫ ν) hi

theorem polynomial_center_functor : (firstPolynomialCenter P u v α ha).1.hom.toFunctor =
    (productPolynomialCenter P u v α hb).1.hom.toFunctor := rfl

/-- The actual product and postcomposition routes agree by the original three-factor coherence. -/
theorem polynomial_center_reference : (firstPolynomialCenter P u v α ha).2 =
    (productPolynomialCenter P u v α hb).2 := by
  have he : eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (chartMiddleGeom P u α ha)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor =
    chartIso P u v α hb ≪≫
      isoWhiskerLeft (BoundedFlatCoefficientSquareFamilies.polynomialSource P u).hom.toFunctor
      (BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  rw [he]
  change smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
    (first_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
        (chartMiddleGeom P u α ha)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso (coefficientMap P (α.app b))
          (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)))
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (chart_total P u v α hb).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (chartMiddleGeom P u α ha) (chart_total P u v α hb).symm (first_total P u v).symm).symm

/-- The full original central nodes agree; no matching-functor quotient is taken. -/
theorem first_product_polynomial_center :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (firstIso P u v) (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha 5) =
      BoundedFlatCoefficientBassH1References.chartNodes P u v α hb 2 := by
  rw [first_polynomial_center_original, product_polynomial_center_original]
  apply ModelSimplex.reference_node_eq (polynomial_center_functor P u v α ha hb)
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg Iso.hom (polynomial_center_reference P u v α ha hb)

/-- Actual positive first/product-column center, including its entire reference iso. -/
theorem plus_column_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 5 =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurent R)
      (laurentPlus_projection P b) 2 :=
  first_product_polynomial_center P u v (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P b)

/-- The distinct inverse first/product-column center retains the original inverse projection. -/
theorem minus_column_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 16 =
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P b) 2 :=
  first_product_polynomial_center P u v (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P b)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
