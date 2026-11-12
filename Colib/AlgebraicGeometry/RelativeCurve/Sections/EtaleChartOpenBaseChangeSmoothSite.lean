/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartSmoothSite

/-! # Native smooth-site promotion on the good tail open

All schemes are the original literal pullbacks and all objects remain over S.
The old chart target is recovered by the actual second projection.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange

variable {S : Scheme.{u}} {A Y Z : SmoothSite S}
  [hA : IsAffine A.left] [hY : IsAffine Y.left] [hZ : IsAffine Z.left]
  (q : A ⟶ Z) [hq : Etale q.left] (p : Z ⟶ Y) [hp : Smooth p.left]
  (s : Y ⟶ Z) (hs : s.left ≫ p.left = 𝟙 Y.left)
  {V : Scheme.{u}} [hV : IsAffine V] (k : V ⟶ Y.left) [IsOpenImmersion k]

local instance affine_k : IsAffineHom k :=
  @isAffineHom_of_isAffine V Y.left k inferInstance inferInstance

/-- The unchanged good tail, over the original base. -/
def tailSite : SmoothSite S := SmoothSite.mk (k ≫ Y.hom)

instance tailSite_isAffine : IsAffine (tailSite k).left :=
  inferInstanceAs (IsAffine V)

local instance native_projection_smooth :
    Smooth (Scheme.EtaleChart.MarkedBaseChange.projection p.left k) :=
  inferInstanceAs (Smooth (pullback.fst k p.left))

omit hA hY hZ hp hV [IsOpenImmersion k] in
theorem native_chart_etale :
    Etale (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (Scheme.EtaleChart.MarkedBaseChange.chartMap_isPullback q.left p.left k).flip hq

/-- The actual coordinate pullback, promoted using the existing native API. -/
abbrev coordinateSite : SmoothSite S :=
  @EtaleChart.coordinateSite S (tailSite k) (tailSite_isAffine k)
    (pullback k p.left) (inferInstanceAs (IsAffine (pullback k p.left)))
    (Scheme.EtaleChart.MarkedBaseChange.projection p.left k)
    (native_projection_smooth p k)

/-- The actual chart pullback, not a replacement by an isomorphic chart. -/
abbrev chartSite : SmoothSite S :=
  @EtaleChart.chartSite S (tailSite k) (tailSite_isAffine k)
    (pullback k (q.left ≫ p.left)) (pullback k p.left)
    (inferInstanceAs (IsAffine (pullback k (q.left ≫ p.left))))
    (inferInstanceAs (IsAffine (pullback k p.left)))
    (Scheme.EtaleChart.MarkedBaseChange.projection p.left k)
    (native_projection_smooth p k)
    (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k)
    (native_chart_etale q p k)

instance coordinateSite_isAffine : IsAffine (coordinateSite p k).left :=
  inferInstanceAs (IsAffine (pullback k p.left))

instance chartSite_isAffine : IsAffine (chartSite q p k).left :=
  inferInstanceAs (IsAffine (pullback k (q.left ≫ p.left)))

abbrev projection : coordinateSite p k ⟶ tailSite k :=
  @EtaleChart.projection S (tailSite k) (tailSite_isAffine k)
    (pullback k p.left) (inferInstanceAs (IsAffine (pullback k p.left)))
    (Scheme.EtaleChart.MarkedBaseChange.projection p.left k)
    (native_projection_smooth p k)

abbrev chart : chartSite q p k ⟶ coordinateSite p k :=
  @EtaleChart.chart S (tailSite k) (tailSite_isAffine k)
    (pullback k (q.left ≫ p.left)) (pullback k p.left)
    (inferInstanceAs (IsAffine (pullback k (q.left ≫ p.left))))
    (inferInstanceAs (IsAffine (pullback k p.left)))
    (Scheme.EtaleChart.MarkedBaseChange.projection p.left k)
    (native_projection_smooth p k)
    (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k)
    (native_chart_etale q p k)

abbrev sectionMap : tailSite k ⟶ coordinateSite p k :=
  @EtaleChart.sectionMap S (tailSite k) (tailSite_isAffine k)
    (pullback k p.left) (inferInstanceAs (IsAffine (pullback k p.left)))
    (Scheme.EtaleChart.MarkedBaseChange.projection p.left k)
    (native_projection_smooth p k)
    (Scheme.EtaleChart.MarkedBaseChange.sectionMap p.left s.left hs k)
    (Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs k)

instance chart_etale : Etale (chart q p k).left := native_chart_etale q p k

instance projection_smooth : Smooth (projection p k).left := native_projection_smooth p k

theorem section_projection : sectionMap p s hs k ≫ projection p k = 𝟙 (tailSite k) :=
  MorphismProperty.Over.Hom.ext
    (Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs k)

/-- The chart second projection really is over the original base S. -/
theorem chartProjection_over_base :
    pullback.snd k (q.left ≫ p.left) ≫ A.hom = (chartSite q p k).hom := by
  have hA : (q.left ≫ p.left) ≫ Y.hom = A.hom :=
    MorphismProperty.Over.w (q ≫ p)
  have hcalc : pullback.snd k (q.left ≫ p.left) ≫ A.hom =
      (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k ≫
        Scheme.EtaleChart.MarkedBaseChange.projection p.left k) ≫ (k ≫ Y.hom) := by
    calc
      pullback.snd k (q.left ≫ p.left) ≫ A.hom =
          pullback.snd k (q.left ≫ p.left) ≫ ((q.left ≫ p.left) ≫ Y.hom) :=
        congrArg (fun z => pullback.snd k (q.left ≫ p.left) ≫ z) hA.symm
      _ = (pullback.snd k (q.left ≫ p.left) ≫ (q.left ≫ p.left)) ≫ Y.hom :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst k (q.left ≫ p.left) ≫ k) ≫ Y.hom :=
        congrArg (fun z => z ≫ Y.hom) (pullback.condition (f := k) (g := q.left ≫ p.left)).symm
      _ = pullback.fst k (q.left ≫ p.left) ≫ (k ≫ Y.hom) := Category.assoc _ _ _
      _ = (Scheme.EtaleChart.MarkedBaseChange.chartMap q.left p.left k ≫
        Scheme.EtaleChart.MarkedBaseChange.projection p.left k) ≫ (k ≫ Y.hom) :=
        congrArg (fun z => z ≫ (k ≫ Y.hom)) (Scheme.EtaleChart.MarkedBaseChange.chartMap_fst q.left
          p.left k).symm
  exact hcalc.trans (Category.assoc _ _ _)

/-- The original chart target is restricted by its actual projection. -/
def chartToOriginal : chartSite q p k ⟶ A :=
  homMk (pullback.snd k (q.left ≫ p.left)) (chartProjection_over_base q p k)

abbrev target {T : SmoothSite S} (t : A ⟶ T) : chartSite q p k ⟶ T :=
  chartToOriginal q p k ≫ t

theorem target_left {T : SmoothSite S} (t : A ⟶ T) :
    (target q p k t).left = pullback.snd k (q.left ≫ p.left) ≫ t.left := rfl

variable {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
  (hξ : ξ ≫ q.left = η ≫ s.left)
  (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)

/-- The original mark lifted into the chosen good open. -/
abbrev mark : Spec (.of Ω) ⟶ (chartSite q p k).left :=
  Scheme.EtaleChart.MarkedBaseChange.chartMark q.left p.left s.left hs k ξ η hξ ηV hη

include hq in
theorem mark_chart :
    mark q p s hs k ξ η hξ ηV hη ≫ (chart q p k).left =
      ηV ≫ (sectionMap p s hs k).left :=
  Scheme.EtaleChart.MarkedBaseChange.chartMark_coordinate q.left p.left s.left hs k ξ η hξ ηV hη

theorem mark_original :
    mark q p s hs k ξ η hξ ηV hη ≫ (chartToOriginal q p k).left = ξ :=
  Scheme.EtaleChart.MarkedBaseChange.chartMark_original q.left p.left s.left hs k ξ η hξ ηV hη

theorem mark_target {T : SmoothSite S} (t : A ⟶ T) :
    mark q p s hs k ξ η hξ ηV hη ≫ (target q p k t).left = ξ ≫ t.left :=
  Scheme.EtaleChart.MarkedBaseChange.chartMark_target q.left p.left s.left hs k ξ η hξ ηV hη t.left

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OpenBaseChange
