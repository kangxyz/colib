/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChart
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Base change of the same chart and marked section to the good tail open

Take k to be Spec(Away t) → Spec R. Every map below is defined by actual
pullbacks; no global finiteness of the unlocalized boundary is asserted.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart.MarkedBaseChange
/-- Membership of the original field-valued mark in D(t) supplies its actual
lift to Spec(Away t); no new mark is chosen. -/
theorem exists_mark_localizationAway {R Ω : Type u} [CommRing R] [Field Ω]
    (η : Spec (.of Ω) ⟶ Spec (.of R)) (t : R)
    (ht : t ∉ (η default).asIdeal) :
    ∃ ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)),
      ηV ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) = η := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen t
  have hk : Set.range k = (U : Set (Spec (.of R))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away t) t
  have hη : Set.range η ⊆ Set.range k := by
    rintro _ ⟨z, rfl⟩
    apply (Set.ext_iff.mp hk (η z)).mpr
    change t ∉ (η z).asIdeal
    exact Eq.mpr (congrArg (fun a : Spec (.of Ω) => t ∉ (η a).asIdeal)
      (Subsingleton.elim z default)) ht
  exact ⟨IsOpenImmersion.lift k η hη, IsOpenImmersion.lift_fac k η hη⟩

variable {A Y Z V : Scheme.{u}} (q : A ⟶ Z) (p : Z ⟶ Y)
  (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) (k : V ⟶ Y)

/-- The coordinate scheme after the actual change of the tail base. -/
abbrev coordinate := pullback k p
/-- The original chart after the same change of the tail base. -/
abbrev chart := pullback k (q ≫ p)
/-- The actual coordinate projection to the new tail base. -/
abbrev projection : coordinate p k ⟶ V := pullback.fst k p

instance coordinate_isAffine [IsAffine Y] [IsAffine Z] [IsAffine V] :
    IsAffine (coordinate p k) := inferInstanceAs (IsAffine (pullback k p))

instance chart_isAffine [IsAffine Y] [IsAffine A] [IsAffine V] :
    IsAffine (chart q p k) := inferInstanceAs (IsAffine (pullback k (q ≫ p)))

instance projection_smoothOfRelativeDimension (d : ℕ) [SmoothOfRelativeDimension d p] :
    SmoothOfRelativeDimension d (projection p k) :=
  inferInstanceAs (SmoothOfRelativeDimension d (pullback.fst k p))

/-- The unchanged chart after the actual base change. -/
def chartMap : chart q p k ⟶ coordinate p k :=
  pullback.lift (pullback.fst k (q ≫ p)) (pullback.snd k (q ≫ p) ≫ q)
    ((pullback.condition (f := k) (g := q ≫ p)).trans
      (Category.assoc _ _ _).symm)

@[reassoc] theorem chartMap_fst : chartMap q p k ≫ pullback.fst k p =
    pullback.fst k (q ≫ p) := pullback.lift_fst _ _ _
@[reassoc] theorem chartMap_snd : chartMap q p k ≫ pullback.snd k p =
    pullback.snd k (q ≫ p) ≫ q := pullback.lift_snd _ _ _

/-- The chart map is the base change of the original q. -/
theorem chartMap_isPullback :
    IsPullback (chartMap q p k) (pullback.snd k (q ≫ p)) (pullback.snd k p) q := by
  refine IsPullback.of_right (h₁₂ := pullback.fst k p)
    (h₂₂ := p) (v₁₃ := k) ?_ (chartMap_snd q p k)
    (IsPullback.of_hasPullback k p)
  simpa only [chartMap_fst] using (IsPullback.of_hasPullback k (q ≫ p))

instance [Etale q] : Etale (chartMap q p k) :=
  MorphismProperty.of_isPullback (P := @Etale) (chartMap_isPullback q p k).flip inferInstance

/-- The original section, restricted rather than replaced. -/
def sectionMap : V ⟶ coordinate p k :=
  pullback.lift (𝟙 V) (k ≫ s) (by
    exact (Category.id_comp k).trans
      ((Category.comp_id k).symm.trans
        ((congrArg (fun z => k ≫ z) hs.symm).trans (Category.assoc _ _ _).symm)))

theorem sectionMap_projection : sectionMap p s hs k ≫ projection p k = 𝟙 V :=
  pullback.lift_fst _ _ _
@[reassoc] theorem sectionMap_original : sectionMap p s hs k ≫ pullback.snd k p = k ≫ s :=
  pullback.lift_snd _ _ _

variable {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y)
  (hξ : ξ ≫ q = η ≫ s)
  (ηV : Spec (.of Ω) ⟶ V) (hη : ηV ≫ k = η)

/-- The lift uses the same mark and the chosen lift into the good tail open. -/
def chartMark : Spec (.of Ω) ⟶ chart q p k :=
  pullback.lift ηV ξ (hη.trans (Scheme.EtaleChart.mark_base q p s ξ η hξ hs).symm)

@[reassoc] theorem chartMark_original : chartMark q p s hs k ξ η hξ ηV hη ≫
    pullback.snd k (q ≫ p) = ξ := pullback.lift_snd _ _ _

theorem chartMark_coordinate : chartMark q p s hs k ξ η hξ ηV hη ≫ chartMap q p k =
    ηV ≫ sectionMap p s hs k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chartMap_fst, sectionMap_projection,
      Category.comp_id, chartMark, pullback.lift_fst]
  · simp only [Category.assoc, chartMap_snd, sectionMap_original]
    rw [← Category.assoc, chartMark_original, hξ, ← Category.assoc, hη]

/-- Any original target map is preserved by this same projection. -/
theorem chartMark_target {T : Scheme.{u}} (t : A ⟶ T) :
    chartMark q p s hs k ξ η hξ ηV hη ≫ (pullback.snd k (q ≫ p) ≫ t) = ξ ≫ t :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ t) (chartMark_original q p s hs k ξ η hξ ηV hη))

end AlgebraicGeometry.Scheme.EtaleChart.MarkedBaseChange
