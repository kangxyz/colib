/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartBottomSourceReferences

/-!
# The remaining shared Bass chart-bottom references

The actual chart and bottom families each take the same first and total
normalization steps after their shared positive or inverse source. Adapted
from `ChartLastReferences.lean`, `CoefficientReferenceSteps.lean`, and
`BassSharedNodes.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u v

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassChartBottomReferences

open BoundedFlatCoefficientBassBottomCommonFamily BoundedFlatCoefficientBassOverlap
open BoundedFlatPerfectReferenceCoherence CommonReferenceProduct

local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

section ChartLast

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The raw normalization intermediate follows the source through the original first piece. -/
theorem last_intermediate_reference :
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 16).2 =
      (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 ≪≫
        smallIso (isoWhiskerLeft (N a)
          (BoundedFlatPerfectBinarySimplex.geometricIso q' p')) := by
  change _ ≪≫ (_ ≪≫ _) = (_ ≪≫ _) ≪≫ _
  exact (Iso.trans_assoc _ _ _).symm

/-- The final chart reference is the same source followed by the native total normalization iso. -/
theorem last_target_reference :
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 17).2 =
      (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 ≪≫
        smallIso (isoWhiskerLeft (N a)
          (NC q' p')) := by
  apply Iso.ext
  change (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq).hom ≫
      ((BoundedFlatPerfectTripleSimplex.leftFirst q' p' a).hom ≫
        (BoundedFlatPerfectTripleSimplex.leftSecond q' p' a).hom) =
    ((BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq).hom ≫
      (BoundedFlatPerfectTripleSimplex.rightFirst q' p' a).hom) ≫
        (BoundedFlatPerfectTripleSimplex.rightSecond q' p' a).hom
  rw [BoundedFlatPerfectTripleSimplex.two_routes, Category.assoc]

end ChartLast

private theorem pair_row_step {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {K : C ⥤ E}
    (a : K ≅ F₀ ⋙ G₀) (e : F₀ ≅ F₁) (f : G₀ ≅ G₁) :
    a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod (Iso.refl G₀))) ≪≫
        isoWhiskerLeft F₁ f := by
  rw [composition_pair_iso, composition_pair_iso, isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.trans_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The first Laurent normalization step whiskered by the projection triangle's target functor
for `g`. -/
abbrev firstStep (g : (space (op P, (laurentUnderFunctor R).obj a)) ⟶
    space (op P, (polynomialUnderFunctor R).obj a)) :=
  isoWhiskerLeft
    (BoundedFlatPerfectBinarySimplex.targetMap g (polynomialProjection P a)).hom.toFunctor
    (BoundedFlatPerfectBinarySimplex.first
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

/-- The total Laurent normalization comparison whiskered by the projection triangle's target
functor for `g`. -/
abbrev totalStep (g : (space (op P, (laurentUnderFunctor R).obj a)) ⟶
    space (op P, (polynomialUnderFunctor R).obj a)) :=
  isoWhiskerLeft
    (BoundedFlatPerfectBinarySimplex.targetMap g (polynomialProjection P a)).hom.toFunctor
    (BoundedFlatPerfectBinarySimplex.total
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

/-- The full chart intermediate reference follows the original first normalization component. -/
theorem chart_first_step (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (chartOverlapNodes P u v α hc 16).2 =
      (chartOverlapNodes P u v α hc 15).2 ≪≫
        firstStep P u v (coefficientMap P (α.app a)) := by
  have hs : (chartNodes P u v α 16).2 =
      (chartNodes P u v α 15).2 ≪≫
        smallIso (isoWhiskerLeft (N (coefficientMap P (α.app a)))
          (BoundedFlatPerfectBinarySimplex.geometricIso
            (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
            (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))) :=
    last_intermediate_reference _ _ _ _ _ _ _ _ _
  change commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor
      (chartNodes P u v α 16).2 =
    (commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor
        (chartNodes P u v α 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

/-- The full chart endpoint reference follows the original total normalized component. -/
theorem chart_total_step (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (chartOverlapNodes P u v α hc 17).2 =
      (chartOverlapNodes P u v α hc 15).2 ≪≫
        totalStep P u v (coefficientMap P (α.app a)) := by
  have hs : (chartNodes P u v α 17).2 =
      (chartNodes P u v α 15).2 ≪≫
        smallIso (isoWhiskerLeft (N (coefficientMap P (α.app a)))
          (NC
            (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
            (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))) :=
    last_target_reference _ _ _ _ _ _ _ _ _
  change commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor
      (chartNodes P u v α 17).2 =
    (commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor
        (chartNodes P u v α 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

theorem bottom_plus_first_step : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 43).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 42).2
      ≪≫ firstStep P u v (laurentPlus P a) :=
  pair_row_step (referenceIso P u v)
    (BoundedFlatCoefficientBassProjectionPath.nodes P a 2).2
    (BoundedFlatPerfectBinarySimplex.first
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

theorem bottom_plus_total_step : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 44).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 42).2
      ≪≫ totalStep P u v (laurentPlus P a) :=
  pair_row_step (referenceIso P u v)
    (BoundedFlatCoefficientBassProjectionPath.nodes P a 2).2
    (BoundedFlatPerfectBinarySimplex.total
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

theorem bottom_minus_first_step : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 49).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 48).2
      ≪≫ firstStep P u v (laurentMinus P a) :=
  pair_row_step (referenceIso P u v)
    (BoundedFlatCoefficientBassProjectionPath.nodes P a 4).2
    (BoundedFlatPerfectBinarySimplex.first
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

theorem bottom_minus_total_step : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 50).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 48).2
      ≪≫ totalStep P u v (laurentMinus P a) :=
  pair_row_step (referenceIso P u v)
    (BoundedFlatCoefficientBassProjectionPath.nodes P a 4).2
    (BoundedFlatPerfectBinarySimplex.total
      (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v)
      (BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u))

theorem plus_intermediate_reference :
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 16).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 43).2 := by
  change (chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 16).2 = _
  rw [chart_first_step, bottom_plus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep P u v (laurentPlus P a)) (plus_source_reference P u v)

theorem plus_target_reference : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 17).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 44).2 := by
  change (chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 17).2 = _
  rw [chart_total_step, bottom_plus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep P u v (laurentPlus P a)) (plus_source_reference P u v)

theorem minus_intermediate_reference :
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 34).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 49).2 := by
  change (chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 16).2 = _
  rw [chart_first_step, bottom_minus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep P u v (laurentMinus P a)) (minus_source_reference P u v)

theorem minus_target_reference : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 35).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 50).2 := by
  change (chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 17).2 = _
  rw [chart_total_step, bottom_minus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep P u v (laurentMinus P a)) (minus_source_reference P u v)

/-- The actual full positive intermediate node is shared. -/
theorem plus_intermediate_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 16 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 43 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (plus_intermediate_functor P u v)
  · have href := heq_of_eq (plus_intermediate_reference P u v)
    exact href

/-- The actual full positive target node is shared. -/
theorem plus_target_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 17 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 44 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (plus_target_functor P u v)
  · have href := heq_of_eq (plus_target_reference P u v)
    exact href

/-- The actual full inverse intermediate node is shared. -/
theorem minus_intermediate_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 34 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 49 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (minus_intermediate_functor P u v)
  · have href := heq_of_eq (minus_intermediate_reference P u v)
    exact href

/-- The actual full inverse target node is shared. -/
theorem minus_target_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 35 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 50 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (minus_target_functor P u v)
  · have href := heq_of_eq (minus_target_reference P u v)
    exact href

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassChartBottomReferences
