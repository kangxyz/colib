/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange

/-! # The original chart lands in the actual localized retained source

The source is pullback k (q ≫ p). The retained target is literally
pullback (pullback.snd k fN) j, not a definitionally substituted pullback k f.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart.LocalizedRetainedLift

variable {A Z Y V U N : Scheme.{u}}
  (q : A ⟶ Z) (p : Z ⟶ Y) (k : V ⟶ Y)
  (i : A ⟶ U) (f : U ⟶ Y) (hi : i ≫ f = q ≫ p)
  (j : U ⟶ N) (fN : N ⟶ Y) (hj : j ≫ fN = f)

/-- The original localized compactification with its original projections. -/
abbrev model := pullback k fN
/-- The literal retained source used by localized good geometry. -/
abbrev retained := pullback (pullback.snd k fN) j
/-- Its actual structure map to the good tail. -/
abbrev retainedProjection : retained k j fN ⟶ V :=
  pullback.fst (pullback.snd k fN) j ≫ pullback.fst k fN

/-- The original chart inclusion, first lifted to the actual localized model. -/
def chartToModel : MarkedBaseChange.chart q p k ⟶ model k fN :=
  pullback.lift (pullback.fst k (q ≫ p)) (pullback.snd k (q ≫ p) ≫ i ≫ j) (by
    have hij : (i ≫ j) ≫ fN = q ≫ p :=
      (Category.assoc i j fN).trans ((congrArg (fun z => i ≫ z) hj).trans hi)
    exact (pullback.condition (f := k) (g := q ≫ p)).trans
      ((congrArg (fun z => pullback.snd k (q ≫ p) ≫ z) hij.symm).trans
        (Category.assoc _ _ _).symm))

@[reassoc] theorem chartToModel_fst :
    chartToModel q p k i f hi j fN hj ≫ pullback.fst k fN =
      pullback.fst k (q ≫ p) := pullback.lift_fst _ _ _

@[reassoc] theorem chartToModel_snd :
    chartToModel q p k i f hi j fN hj ≫ pullback.snd k fN =
      pullback.snd k (q ≫ p) ≫ i ≫ j := pullback.lift_snd _ _ _

/-- The genuine lift into the literal localized retained source. -/
def inclusion : MarkedBaseChange.chart q p k ⟶ retained k j fN :=
  pullback.lift (chartToModel q p k i f hi j fN hj)
    (pullback.snd k (q ≫ p) ≫ i)
    ((chartToModel_snd q p k i f hi j fN hj).trans (Category.assoc _ _ _).symm)

@[reassoc] theorem inclusion_model :
    inclusion q p k i f hi j fN hj ≫ pullback.fst (pullback.snd k fN) j =
      chartToModel q p k i f hi j fN hj := pullback.lift_fst _ _ _

@[reassoc] theorem inclusion_original :
    inclusion q p k i f hi j fN hj ≫ pullback.snd (pullback.snd k fN) j =
      pullback.snd k (q ≫ p) ≫ i := pullback.lift_snd _ _ _

/-- The required hi_t equation, with the actual localized chart q_t and p_t. -/
theorem inclusion_structure :
    inclusion q p k i f hi j fN hj ≫ retainedProjection k j fN =
      MarkedBaseChange.chartMap q p k ≫ MarkedBaseChange.projection p k := by
  have h := (Category.assoc (inclusion q p k i f hi j fN hj)
    (pullback.fst (pullback.snd k fN) j) (pullback.fst k fN)).symm
  exact h.trans ((congrArg (fun z => z ≫ pullback.fst k fN)
    (inclusion_model q p k i f hi j fN hj)).trans
      ((chartToModel_fst q p k i f hi j fN hj).trans
        (MarkedBaseChange.chartMap_fst q p k).symm))

/-- No target is extended to the whole compactification. -/
theorem inclusion_target {T : Scheme.{u}} (t : U ⟶ T) :
    inclusion q p k i f hi j fN hj ≫ (pullback.snd (pullback.snd k fN) j ≫ t) =
      pullback.snd k (q ≫ p) ≫ (i ≫ t) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ t) (inclusion_original q p k i f hi j fN hj)).trans
      (Category.assoc _ _ _))

/-- The same lifted original mark has the same original retained target. -/
theorem marked_target {Ω : Type u} [Field Ω]
    (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y)
    (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y)
    (hξ : ξ ≫ q = η ≫ s) (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)
    {T : Scheme.{u}} (t : U ⟶ T) :
    MarkedBaseChange.chartMark q p s hs k ξ η hξ ηV hη ≫
      (inclusion q p k i f hi j fN hj ≫
        (pullback.snd (pullback.snd k fN) j ≫ t)) = ξ ≫ (i ≫ t) :=
  (congrArg (fun z => MarkedBaseChange.chartMark q p s hs k ξ η hξ ηV hη ≫ z)
    (inclusion_target q p k i f hi j fN hj t)).trans
      (MarkedBaseChange.chartMark_target q p s hs k ξ η hξ ηV hη (i ≫ t))

end AlgebraicGeometry.Scheme.EtaleChart.LocalizedRetainedLift
