/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartBottomSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectReferenceCoherence
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# The actual shared references at the two Bass chart-bottom source nodes

Both signed charts are compared to the same common Laurent anchor using the
original normalized pullback associativity. The inverse chart retains its
original geometric source transport. Adapted from `ChartLastReferences.lean`
and `CoefficientSourceReferences.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

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

/-- The last chart source retains its literal equality-transported binary comparison. -/
theorem last_source_reference :
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 =
      smallIso (eqToIso (congrArg N
        (DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm) ≪≫
          NC (q' ≫ p') a) := by
  change smallIso (eqToIso (congrArg N
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))) ≪≫
    smallIso (eqToIso (congrArg N (Category.assoc q' p' a).symm) ≪≫
      NC (q' ≫ p') a) = _
  rw [← smallIso_trans]
  apply congrArg smallIso
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, eqToHom_trans]

end ChartLast

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The composite Laurent coefficient scheme map, applying the map for `v` before the map for
`u`. -/
abbrev laurentComposite := coefficientMap P ((laurentUnderFunctor R).map v) ≫
  coefficientMap P ((laurentUnderFunctor R).map u)
/-- The chart map at `c` followed by the polynomial coefficient scheme maps for `v` and `u`. -/
abbrev chartComposite (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :=
  coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
    coefficientMap P ((polynomialUnderFunctor R).map u)

/-- The two original naturality equations identify the actual chart's final geometric total. -/
theorem chart_equation (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :
    chartComposite P u v α = laurentComposite P u v ≫ coefficientMap P (α.app a) :=
  (DoubleSquareTrack.total_eq
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (by rw [← coefficientMap_comp, ← coefficientMap_comp, α.naturality])
    (by rw [← coefficientMap_comp, ← coefficientMap_comp, α.naturality])).symm

/-- The chart source reference is precisely the original equality-transported left route. -/
theorem chart_source_reference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (chartOverlapNodes P u v α hc 15).2 =
      smallIso ((eqToIso (congrArg N
        (chart_total P u v α hc).symm) ≪≫
          NC (chartComposite P u v α) (polynomialProjection P a))
        ≪≫ isoWhiskerLeft (N (polynomialProjection P a))
          (eqToIso (congrArg N (chart_equation P u v α)) ≪≫
            NC (laurentComposite P u v)
              (coefficientMap P (α.app a)))) := by
  have he : (chartNodes P u v α 15).2 =
      smallIso (eqToIso (congrArg N (chart_equation P u v α)) ≪≫
        NC (laurentComposite P u v)
          (coefficientMap P (α.app a))) :=
    last_source_reference _ _ _ _ _ _ _ _ _
  change commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor
      (chartNodes P u v α 15).2 = _
  rw [he]
  change smallIso (eqToIso (congrArg N
      (chart_total P u v α hc).symm) ≪≫
        NC (chartComposite P u v α)
          (polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙
      N (polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg N (chart_equation P u v α)) ≪≫
        NC (laurentComposite P u v)
          (coefficientMap P (α.app a)))) = _
  rw [smallIso_precomp, ← smallIso_trans]

/-- The native positive bottom source reference retains the actual binary normalization iso. -/
theorem bottom_plus_source_reference :
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 42).2 =
    smallIso ((eqToIso (congrArg N
      (bottom_total P u v).symm) ≪≫
        NC (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
      isoWhiskerRight
        (NC (laurentPlus P a) (polynomialProjection P a))
        (N (laurentComposite P u v))) := by
  change referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BoundedFlatCoefficientBassProjectionPath.nodes P a 2).2.prod
        (Iso.refl (BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor)) = _
  rw [composition_pair_iso_other, isoWhiskerLeft_refl, Iso.refl_trans]
  change smallIso (eqToIso (congrArg N
      (bottom_total P u v).symm) ≪≫
        NC (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (NC
      (laurentPlus P a) (polynomialProjection P a)))
      (AsSmall.down ⋙ N (laurentComposite P u v) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- The native negative bottom reference retains the exact positive-to-negative source transport. -/
theorem bottom_minus_source_reference :
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 48).2 =
    smallIso ((eqToIso (congrArg N
      (bottom_total P u v).symm) ≪≫
        NC (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
      isoWhiskerRight
        (eqToIso (congrArg N
          ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)) ≪≫
          NC (laurentMinus P a) (polynomialProjection P a))
        (N (laurentComposite P u v))) := by
  change referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BoundedFlatCoefficientBassProjectionPath.nodes P a 4).2.prod
        (Iso.refl (BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor)) = _
  rw [composition_pair_iso_other, isoWhiskerLeft_refl, Iso.refl_trans]
  have he : BoundedFlatCoefficientBassProjectionPath.sourceIso P a = smallIso (eqToIso
      (congrArg N
        ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm))) :=
    (smallIso_eqToIso _).symm
  change referenceIso P u v ≪≫
    isoWhiskerRight (BoundedFlatCoefficientBassProjectionPath.sourceIso P a ≪≫
      smallIso (NC
        (laurentMinus P a) (polynomialProjection P a)))
      (BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor = _
  rw [he, ← smallIso_trans]
  change smallIso (eqToIso (congrArg N
      (bottom_total P u v).symm) ≪≫
        NC (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg N
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)) ≪≫
        NC (laurentMinus P a) (polynomialProjection P a)))
      (AsSmall.down ⋙ N (laurentComposite P u v) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- Full anchored reference equality for the positive source node. -/
theorem plus_source_reference : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 15).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 42).2 := by
  change (chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 15).2 = _
  rw [chart_source_reference, bottom_plus_source_reference]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc, laurentPlus] using
    anchored_factorizations_strict (laurentComposite P u v) (laurentPlus P a)
      (polynomialProjection P a) (chartComposite P u v (underToLaurent R))
      (laurentPlus P a ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chart_equation P u v (underToLaurent R)) rfl
      (chart_total P u v (underToLaurent R) (laurentPlus_projection P c)).symm
      (bottom_total P u v).symm

/-- Full anchored reference equality for the inverse source node, including source transport. -/
theorem minus_source_reference : (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 33).2 =
    (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 48).2 := by
  change (chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 15).2 = _
  rw [chart_source_reference, bottom_minus_source_reference]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc, laurentMinus] using
    anchored_factorizations_strict (laurentComposite P u v) (laurentMinus P a)
      (polynomialProjection P a) (chartComposite P u v (underToLaurentInvert R))
      (laurentPlus P a ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chart_equation P u v (underToLaurentInvert R))
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)
      (chart_total P u v (underToLaurentInvert R) (laurentMinus_projection P c)).symm
      (bottom_total P u v).symm

/-- The actual full positive source node is shared. -/
theorem plus_source_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 15 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 42 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (plus_source_functor P u v)
  · have href := heq_of_eq (plus_source_reference P u v)
    exact href

/-- The actual full inverse source node is shared, including its original transport. -/
theorem minus_source_node : BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 33 =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v 48 := by
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (minus_source_functor P u v)
  · have href := heq_of_eq (minus_source_reference P u v)
    exact href

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassChartBottomReferences
