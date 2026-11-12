/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.CompactificationAffineBaseChange
public import Colib.AlgebraicGeometry.Morphisms.Finite.SpecAwayBaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleBoundaryDiagram

/-! # Actual localized full-boundary geometry on the original good tail open

Only the restriction of the original full boundary to D(t) is assumed finite.
The original finite cover and each of the two distinct charts are transported
through the same localization map. A genuine lifted mark supplies nonemptiness.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.QuadraticLocalized
variable {R : Type u} [CommRing R] (t : R)
  {N U D : Scheme.{u}} (p : N ⟶ Spec (.of R))

/-- The canonical localization morphism for the chosen good tail open. -/
abbrev scalar : Spec (.of (Localization.Away t)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
/-- The original compactification after the actual localization base change. -/
abbrev model := quadraticCompactificationBaseChange p (algebraMap R (Localization.Away t))
/-- The second projection to the unchanged original compactification. -/
abbrev toOriginal : model t p ⟶ N := pullback.snd (scalar t) p
/-- The structure map of the localized compactification to the good tail. -/
abbrev projection : model t p ⟶ Spec (.of (Localization.Away t)) := pullback.fst (scalar t) p
/-- The literal pullback of the selected original chart into the localized model. -/
abbrev chart (j : U ⟶ N) := pullback (toOriginal t p) j
/-- The first projection of the actual localized chart pullback. -/
abbrev chartInclusion (j : U ⟶ N) : chart t p j ⟶ model t p := pullback.fst _ _

/-- The entire original boundary pulled back to the same good tail. -/
abbrev boundary (d : D ⟶ N) := pullback (scalar t) (d ≫ p)
/-- The canonical map from the whole localized boundary to its model. -/
abbrev boundaryInclusion (d : D ⟶ N) : boundary t p d ⟶ model t p :=
  SmoothSite.etaleBoundaryBaseChangeMap (scalar t) p d

/-- The whole localized boundary is closed, not just a finite subset of it. -/
instance boundary_closed (d : D ⟶ N) [IsClosedImmersion d] :
    IsClosedImmersion (boundaryInclusion t p d) := inferInstanceAs
  (IsClosedImmersion (SmoothSite.etaleBoundaryBaseChangeMap (scalar t) p d))

/-- Local finiteness on the chosen D(t) is sufficient for this actual localized
boundary. No global IsFinite(d ≫ p) is requested or inferred. -/
theorem boundary_finite (d : D ⟶ N)
    [IsFinite ((d ≫ p) ∣_ PrimeSpectrum.basicOpen t)] :
    IsFinite (boundaryInclusion t p d ≫ projection t p) := by
  have hf : IsFinite (pullback.fst (scalar t) (d ≫ p)) :=
    isFinite_pullback_fst_specAway_of_morphismRestrict (d ≫ p) t
  exact (congrArg IsFinite
    (SmoothSite.etaleBoundaryBaseChangeMap_fst (scalar t) p d)).mpr hf

/-- Its range is the entire complement of the same localized retained chart. -/
theorem boundary_complement (j : U ⟶ N) (d : D ⟶ N)
    (hd : Set.range d = (Set.range j)ᶜ) :
    Set.range (boundaryInclusion t p d) = (Set.range (chartInclusion t p j))ᶜ := by
  have range_pb {P X Y S : Scheme.{u}}
      {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
      (hp : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
    rw [← hp.isoPullback_hom_fst]
    change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
    rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
  have hb := range_pb (SmoothSite.etaleBoundaryBaseChangeMap_isPullback (scalar t) p d)
  have hj := Scheme.Pullback.range_fst (toOriginal t p) j
  exact hb.trans ((congrArg (fun z : Set N => toOriginal t p ⁻¹' z) hd).trans
    (congrArg (fun z => zᶜ) hj).symm)

variable (π : N ⟶ projectiveLine R)
  (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = p)

/-- The original finite projective-line cover after the same base change. -/
abbrev cover : model t p ⟶ projectiveLine (Localization.Away t) :=
  quadraticCompactificationBaseChangeCover p (algebraMap R (Localization.Away t)) π hπ

instance cover_finite [IsFinite π] : IsFinite (cover t p π hπ) :=
  inferInstanceAs (IsFinite (quadraticCompactificationBaseChangeCover p
    (algebraMap R (Localization.Away t)) π hπ))

theorem cover_structure : cover t p π hπ ≫
    (projectiveLine (Localization.Away t) ↘ Spec (.of (Localization.Away t))) =
      projection t p :=
  quadraticCompactificationBaseChangeCover_structure p
    (algebraMap R (Localization.Away t)) π hπ

variable (j : U ⟶ N) (a : U ⟶ Spec (.of (Polynomial R)))
  (ha : a ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = j ≫ p)

/-- Use once for the retained chart and once for the distinct independent chart. -/
abbrev coordinate : chart t p j ⟶ Spec (.of (Polynomial (Localization.Away t))) :=
  quadraticCompactificationBaseChangeChart p (algebraMap R (Localization.Away t)) j a ha

instance coordinate_etale [Etale a] : Etale (coordinate t p j a ha) :=
  inferInstanceAs (Etale (quadraticCompactificationBaseChangeChart p
    (algebraMap R (Localization.Away t)) j a ha))

theorem coordinate_structure : coordinate t p j a ha ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away t →+*
      Polynomial (Localization.Away t))) = chartInclusion t p j ≫ projection t p :=
  quadraticCompactificationBaseChangeChart_structure p
    (algebraMap R (Localization.Away t)) j a ha

theorem coordinate_original : coordinate t p j a ha ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R (Localization.Away t)))) =
      pullback.snd (toOriginal t p) j ≫ a :=
  affineLineChartOfActualCartesian_map p (algebraMap R (Localization.Away t)) _ _
    (quadraticCompactificationBaseChange_square p (algebraMap R (Localization.Away t))) j a ha

theorem coordinate_cover (hj : j ≫ π = a ≫ projectiveLineXChart R) :
    chartInclusion t p j ≫ cover t p π hπ =
      coordinate t p j a ha ≫ projectiveLineXChart (Localization.Away t) :=
  quadraticCompactificationBaseChangeChart_cover p
    (algebraMap R (Localization.Away t)) π hπ j a ha hj

variable {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ U) (ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))
  (hmark : ηV ≫ scalar t = (ξ ≫ j) ≫ p)

/-- The same original chart mark in the localized compactification. -/
def modelMark : Spec (.of Ω) ⟶ model t p := pullback.lift ηV (ξ ≫ j) hmark
/-- The same mark in the actual localized chart, proving its nonemptiness. -/
def chartMark : Spec (.of Ω) ⟶ chart t p j :=
  pullback.lift (modelMark t p j ξ ηV hmark) ξ (pullback.lift_snd _ _ _)

theorem chartMark_original : chartMark t p j ξ ηV hmark ≫
    pullback.snd (toOriginal t p) j = ξ := pullback.lift_snd _ _ _

include ξ ηV hmark in
theorem chart_nonempty : Nonempty (chart t p j) :=
  ⟨chartMark t p j ξ ηV hmark default⟩

include ξ ηV hmark in
/-- Integrality is preserved here because the actual localized model is a
nonempty open of N. Nonemptiness is proved by the same supplied mark. -/
theorem model_integral [IsIntegral N] : IsIntegral (model t p) := by
  let : Nonempty (model t p) := ⟨modelMark t p j ξ ηV hmark default⟩
  exact isIntegral_of_isOpenImmersion (toOriginal t p)

/-- Original target maps survive localization on the same marked chart. -/
theorem chartMark_target {T : Scheme.{u}} (f : U ⟶ T) :
    chartMark t p j ξ ηV hmark ≫ (pullback.snd (toOriginal t p) j ≫ f) = ξ ≫ f :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ f) (chartMark_original t p j ξ ηV hmark))

end AlgebraicGeometry.Scheme.QuadraticLocalized
