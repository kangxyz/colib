/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1FirstPolynomialRow

/-!
# The original chart product and old chart share their entire outer words

The proved normalized endpoint determines the first binary piece. Its
source identifies the other binary piece while keeping its original
geometric comparison. Both signed words are then recovered in the old62
family. Adapted from `PreReferenceFamily.lean`, `H1ProductOuterRows.lean`,
and `H1OuterNodeJoins.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
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

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The old middle-right row retains its original reference under both fixed precompositions. -/
theorem old_product_middle_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) := by
  refine ⟨BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a)).hom.toFunctor
      (rightRowReference (BoundedFlatCoefficientBassOverlap.chartReference P u v α)
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u))
        (oldMiddleTripleReference P u v α)), fun i ↦ ?_⟩
  have hn := congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc))
    (merged_middle_right_row
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientMap_naturality_of_natTrans P α u).symm
      (coefficientMap_naturality_of_natTrans P α v).symm i)
  exact hn.trans (pre_pre_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (BoundedFlatCoefficientSquareFamilies.chartSource P v α) _
    (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc) _)

/-- The old first-right row uses the exact first-triple reference under those same maps. -/
theorem old_product_first_representation : ∃ ρ, ∀ i : Fin 3,
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) := by
  refine ⟨BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a)).hom.toFunctor
      (rightRowReference (BoundedFlatCoefficientBassOverlap.chartReference P u v α)
        (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
        (coefficientMap P ((polynomialUnderFunctor R).map u)) (Iso.refl _)), fun i ↦ ?_⟩
  have hn := congrArg (preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
      (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc))
    (merged_first_right_row
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientMap_naturality_of_natTrans P α u).symm
      (coefficientMap_naturality_of_natTrans P α v).symm i)
  exact hn.trans (pre_pre_node (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (BoundedFlatPerfectBinarySimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v))) _
    (BoundedFlatCoefficientBassOverlap.commonToChartReference P u v α hc) _)

include ha

/-- Full-node endpoint cancellation fixes the complete first product row. -/
theorem product_old_outer_first_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (2, BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) := by
  obtain ⟨ρ, hρ⟩ := product_outer_first_representation P u v α hb
  obtain ⟨σ, hσ⟩ := old_product_middle_representation P u v α hc
  exact pre_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (outerProductPre P u)
    (BoundedFlatCoefficientSquareFamilies.chartSource P v α)
    (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
    hρ hσ 2 (product_old_outer_endpoint P u v α ha hb hc) i

/-- The full outer center, with its literal product and old-chart indices. -/
theorem product_old_outer_center : BoundedFlatCoefficientBassH1References.chartNodes P u v α hb 10 =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc 9 :=
  product_old_outer_first_nodes P u v α ha hb hc 0

/-- The other complete product row retains the same proved full source node. -/
theorem product_old_outer_second_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb
      (SimplexGrid.index 4 4
        (2, BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) := by
  obtain ⟨ρ, hρ⟩ := product_outer_second_representation P u v α hb
  obtain ⟨σ, hσ⟩ := old_product_first_representation P u v α hc
  exact pre_families_match (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (outerProductPre P u)
    (BoundedFlatPerfectBinarySimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (binaryNodes (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v))) hρ hσ
    0 (product_old_outer_center P u v α ha hb hc) i


omit ha

section SignedWords

/-- The other half uses the actual varying-family product row and its unchanged full references. -/
theorem product_old_chart_word_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v α hb (SimplexGrid.index 4 4 (2, i)) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc (outerProductWordIndex i) := by
  fin_cases i
  · exact product_old_outer_first_nodes P u v α ha hb hc 0
  · exact product_old_outer_first_nodes P u v α ha hb hc 1
  · exact product_old_outer_first_nodes P u v α ha hb hc 2
  · exact product_old_outer_second_nodes P u v α ha hb hc 1
  · exact product_old_outer_second_nodes P u v α ha hb hc 2

/-- The whole positive product outer row agrees with the unchanged second half of the old chart. -/
theorem product_old62_plus_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurent R)
      (laurentPlus_projection P b)
      (SimplexGrid.index 4 4 (2, i)) =
    BoundedFlatCoefficientBassH0Merged.nodes P u v (BoundedFlatCoefficientBassH0Merged.oldIndex
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (outerProductWordIndex i)))) :=
  (product_old_chart_word_nodes P u v (underToLaurent R) (laurentPlus_projection P a)
    (laurentPlus_projection P b) (laurentPlus_projection P c) i).trans
    ((BoundedFlatCoefficientBassOldChartBinaryRows.old_plus_node P u v _).symm.trans
      (BoundedFlatCoefficientBassH0Merged.old_nodes P u v _).symm)

/-- The whole inverse product row retains its original second-half inverse chart references. -/
theorem product_old62_minus_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.chartNodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P b)
      (SimplexGrid.index 4 4 (2, i)) =
    BoundedFlatCoefficientBassH0Merged.nodes P u v (BoundedFlatCoefficientBassH0Merged.oldIndex
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (outerProductWordIndex i)))) :=
  (product_old_chart_word_nodes P u v (underToLaurentInvert R) (laurentMinus_projection P a)
    (laurentMinus_projection P b) (laurentMinus_projection P c) i).trans
    ((BoundedFlatCoefficientBassOldChartBinaryRows.old_minus_node P u v _).symm.trans
      (BoundedFlatCoefficientBassH0Merged.old_nodes P u v _).symm)

end SignedWords

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
