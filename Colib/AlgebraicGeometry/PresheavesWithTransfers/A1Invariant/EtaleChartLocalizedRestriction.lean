/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleChartOriginalRestriction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartOpenBaseChangeSmoothSite
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartLocalizedRetainedLift
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LocalizedGoodGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LocalizedGeometryInstances
public import Colib.AlgebraicGeometry.Sites.Etale.StrictHenselizationBaseUnits

/-! # Same-good-open input for the actual original chart restriction

Only boundary finiteness on D(tGood) is used. The old field and presheaf remain
unchanged. The localized retained source is the actual nested pullback.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.LocalizedRestriction

variable {K : Type u} [Field K] {R : Type u} [CommRing R]
  (tail : Spec (.of R) ⟶ Spec (.of K))
  [Smooth tail] [IsSeparated tail] [QuasiCompact tail]

local instance nativeTailAffine : IsAffine (SmoothSite.mk tail).left :=
  inferInstanceAs (IsAffine (Spec (.of R)))

variable
  {A Z T : SmoothSite (Spec (.of K))} [hA : IsAffine A.left] [hZ : IsAffine Z.left]
  (q : A ⟶ Z) [hq : Etale q.left] (p : Z ⟶ SmoothSite.mk tail) [hp : Smooth p.left]
  (s : SmoothSite.mk tail ⟶ Z) (hs : s.left ≫ p.left = 𝟙 _)
  (tGood : R)



/-- The native localization map, with no alias search in later constructors. -/
local instance scalar_isOpenImmersion : IsOpenImmersion (QuadraticLocalized.scalar tGood) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away tGood)))))

/-- Fully explicit native projection; all alias-sensitive instances are supplied. -/
abbrev localizedProjection :=
  @OpenBaseChange.projection (Spec (.of K)) (SmoothSite.mk tail) Z
    (nativeTailAffine tail) hZ p hp
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

/-- Fully explicit native chart on the same literal pullback. -/
abbrev localizedChart :=
  @OpenBaseChange.chart (Spec (.of K)) A (SmoothSite.mk tail) Z
    hA (nativeTailAffine tail) hZ q hq p hp
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

/-- Fully explicit native section, preserving the original section map. -/
abbrev localizedSection :=
  @OpenBaseChange.sectionMap (Spec (.of K)) (SmoothSite.mk tail) Z
    (nativeTailAffine tail) hZ p hp s hs
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

/-- Native section identity on the same good tail. -/
theorem localized_section_law : ((localizedSection tail p s hs tGood)).left ≫ ((localizedProjection
  tail p tGood)).left = 𝟙 _ :=
  Scheme.EtaleChart.MarkedBaseChange.sectionMap_projection p.left s.left hs
    (QuadraticLocalized.scalar tGood)

/-- The native localized tail, with explicit object-building instances. -/
abbrev localizedTailSite :=
  @OpenBaseChange.tailSite (Spec (.of K)) (SmoothSite.mk tail) (nativeTailAffine tail)
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

/-- The actual coordinate pullback with explicit native structure instances. -/
abbrev localizedCoordinateSite :=
  @OpenBaseChange.coordinateSite (Spec (.of K)) (SmoothSite.mk tail) Z
    (nativeTailAffine tail) hZ p hp
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

/-- The actual chart pullback with explicit native structure instances. -/
abbrev localizedChartSite :=
  @OpenBaseChange.chartSite (Spec (.of K)) A (SmoothSite.mk tail) Z
    hA (nativeTailAffine tail) hZ q hq p hp
    (Spec (.of (Localization.Away tGood)))
    (inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood)))))
    (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

local instance localizedTailAffine : IsAffine (localizedTailSite tail tGood).left :=
  inferInstanceAs (IsAffine (Spec (.of (Localization.Away tGood))))

local instance localizedCoordinateAffine :
    IsAffine (localizedCoordinateSite tail p tGood).left := by
  let : IsAffine (SmoothSite.mk tail).left := nativeTailAffine tail
  let : IsAffine Z.left := hZ
  exact @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
    (Spec (.of (Localization.Away tGood))) Z.left (SmoothSite.mk tail).left
    (QuadraticLocalized.scalar tGood) p.left inferInstance hZ (nativeTailAffine tail)

local instance localizedChartAffine : IsAffine (localizedChartSite tail q p tGood).left :=
  inferInstanceAs (IsAffine (pullback (QuadraticLocalized.scalar tGood) (q.left ≫ p.left)))

local instance localizedProjectionSmooth :
    Smooth (localizedProjection tail p tGood).left :=
  @OpenBaseChange.projection_smooth (Spec (.of K)) (SmoothSite.mk tail) Z
    (nativeTailAffine tail) hZ p hp (Spec (.of (Localization.Away tGood)))
    inferInstance (QuadraticLocalized.scalar tGood) (scalar_isOpenImmersion tGood)

local instance localizedChartEtale : Etale (localizedChart tail q p tGood).left :=
  OpenBaseChange.native_chart_etale q p (QuadraticLocalized.scalar tGood)

/-- The unchanged native refinement of the actual localized chart. -/
abbrev localizedRefinement :=
  @refinementObject (Spec (.of K))
    (localizedChartSite tail q p tGood) (localizedTailSite tail tGood)
    (localizedCoordinateSite tail p tGood)
    (localizedChartAffine tail q p tGood) (localizedTailAffine tail tGood)
    (localizedCoordinateAffine tail p tGood)
    (localizedChart tail q p tGood) (localizedChartEtale tail q p tGood)
    (localizedProjection tail p tGood) (localizedSection tail p s hs tGood)

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Spec (.of R))
  (hξ : ξ ≫ q.left = η ≫ s.left)
  (ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away tGood)))
  (hη : ηV ≫ (QuadraticLocalized.scalar tGood) = η)


/-- The same lifted mark, on that native refinement. -/
abbrev localizedRefinementPoint :
    GeometricPoint (localizedRefinement tail q p s hs tGood).left :=
  @refinementGeometricPoint (Spec (.of K))
    (localizedChartSite tail q p tGood) (localizedTailSite tail tGood)
    (localizedCoordinateSite tail p tGood)
    (localizedChartAffine tail q p tGood) (localizedTailAffine tail tGood)
    (localizedCoordinateAffine tail p tGood)
    (localizedChart tail q p tGood) (localizedChartEtale tail q p tGood)
    (localizedProjection tail p tGood) (localizedSection tail p s hs tGood)
    Ω inferInstance inferInstance
    (Scheme.EtaleChart.MarkedBaseChange.chartMark q.left p.left s.left hs
      (QuadraticLocalized.scalar tGood) ξ η hξ ηV hη)
    ηV
    (Scheme.EtaleChart.MarkedBaseChange.chartMark_coordinate q.left p.left s.left hs
      (QuadraticLocalized.scalar tGood) ξ η hξ ηV hη)
    (localized_section_law tail p s hs tGood)

/-- The restriction consumer uses the original localized tuple, maps and marks.
The retained smooth/affine facts are derived from its Cartesian geometry. -/
theorem exists_localized_chart_restriction
    (P : PresheafWithTransfers.{v} K) (hP : PresheafWithTransfers.IsA1Invariant P)
    {U N D E : Scheme.{u}} [IsAffine U] [IsIntegral N] [IsNormal N]
    (j : U ⟶ N) [IsOpenImmersion j]
    (fN : N ⟶ Spec (.of R)) [IsProper fN]
    [hSmoothU : SmoothOfRelativeDimension 1 (j ≫ fN)]
    (i : A.left ⟶ U) (hi : i ≫ (j ≫ fN) = q.left ≫ p.left)
    (d : D ⟶ N) [IsClosedImmersion d]
    [hFiniteLocal : IsFinite ((d ≫ fN) ∣_ PrimeSpectrum.basicOpen tGood)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (targetU : U ⟶ T.left) (hTarget : targetU ≫ T.hom = (j ≫ fN) ≫ tail)
    (π : N ⟶ projectiveLine R) [IsFinite π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = fN)
    (aU : U ⟶ Spec (.of (Polynomial R)))
    (haU : aU ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = j ≫ fN)
    (hjπ : j ≫ π = aU ≫ projectiveLineXChart R)
    (eChart : E ⟶ N) [IsOpenImmersion eChart]
    (aE : E ⟶ Spec (.of (Polynomial R))) [Etale aE]
    (haE : aE ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = eChart ≫ fN)
    (heπ : eChart ≫ π = aE ≫ projectiveLineXChart R)
    (ζ : Spec (.of Ω) ⟶ E) (hζ : (ζ ≫ eChart) ≫ fN = η)
    (B : BigEtaleSite.{u}) (hX : B.Contains ((localizedRefinement tail q p s hs tGood)).left)
    (i₀ : SmallEtaleNeighborhood (localizedRefinement tail q p s hs tGood)
      (localizedRefinementPoint tail q p s hs tGood ξ η hξ ηV hη))
    (n : ℕ)
    (hn : ∀ (W : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj W)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K)) :
    let it := Scheme.EtaleChart.LocalizedRetainedLift.inclusion q.left p.left
      (QuadraticLocalized.scalar tGood)
      i (j ≫ fN) hi j fN rfl
    let ft := Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection (QuadraticLocalized.scalar
      tGood) j fN
    let hit := Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
      q.left p.left (QuadraticLocalized.scalar tGood) i (j ≫ fN) hi j fN rfl
    let tt := pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫ targetU
    ∃ (htt : tt ≫ T.hom = ft ≫ (QuadraticLocalized.scalar tGood ≫ tail))
      (Anew : EtaleNeighborhood (localizedRefinement tail q p s hs tGood)
        ((localizedRefinementPoint tail q p s hs tGood ξ η hξ ηV hη)).hom),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫
          OriginalFixed.originalTarget (localizedChart tail q p tGood)
            (localizedProjection tail p tGood)
            (localizedSection tail p s hs tGood) it ft hit tt
            htt).op =
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫
          OriginalFixed.retractTarget (localizedChart tail q p tGood)
            (localizedProjection tail p tGood)
            (localizedSection tail p s hs tGood) it ft hit tt
            htt).op := by
  dsimp only
  let jt := QuadraticLocalized.chartInclusion tGood fN j
  let fNt := QuadraticLocalized.projection tGood fN
  let ft := jt ≫ fNt
  let tt := pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫ targetU
  have hmarkE : ηV ≫ (QuadraticLocalized.scalar tGood) = (ζ ≫ eChart) ≫ fN := hη.trans hζ.symm
  let : IsIntegral (QuadraticLocalized.model tGood fN) :=
    QuadraticLocalized.model_integral tGood fN eChart ζ ηV hmarkE
  let : IsNormal (QuadraticLocalized.model tGood fN) :=
    QuadraticLocalized.model_normal tGood fN
  let : IsProper fNt := inferInstanceAs (IsProper (pullback.fst (QuadraticLocalized.scalar tGood)
    fN))
  let : Nonempty (QuadraticLocalized.chart tGood fN eChart) :=
    QuadraticLocalized.chart_nonempty tGood fN eChart ζ ηV hmarkE
  let : IsFinite (QuadraticLocalized.boundaryInclusion tGood fN d ≫ fNt) :=
    @QuadraticLocalized.boundary_finite R _ tGood N D fN d hFiniteLocal
  -- The following two native geometry calls are supplied by the same-good-open
  -- geometry leaf; they are properties of the literal nested retained source.
  let : IsAffine (QuadraticLocalized.chart tGood fN j) :=
    QuadraticLocalized.retained_isAffine tGood fN j
  let : SmoothOfRelativeDimension 1 ft :=
    @QuadraticLocalized.retained_smoothOfRelativeDimension R _ tGood N U fN j 1 hSmoothU
  have hTargett : tt ≫ T.hom = ft ≫ (QuadraticLocalized.scalar tGood ≫ tail) := by
    have hp := QuadraticLocalized.retained_structure_isPullback tGood fN j
    have hw : pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫ (j ≫ fN) =
        ft ≫ (QuadraticLocalized.scalar tGood) := hp.w
    calc
      tt ≫ T.hom = pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫
          (targetU ≫ T.hom) := Category.assoc _ _ _
      _ = pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫
          ((j ≫ fN) ≫ tail) := congrArg (fun z =>
            pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫ z) hTarget
      _ = (pullback.snd (QuadraticLocalized.toOriginal tGood fN) j ≫ (j ≫ fN)) ≫ tail :=
        (Category.assoc _ _ _).symm
      _ = (ft ≫ (QuadraticLocalized.scalar tGood)) ≫ tail := congrArg (fun z => z ≫ tail) hw
      _ = ft ≫ (QuadraticLocalized.scalar tGood ≫ tail) := Category.assoc _ _ _
  have hnUnit := isUnit_natCast_etaleLocalRing_of_spec_structure
    B ((localizedRefinement tail q p s hs tGood)).left hX (localizedRefinementPoint tail q p s hs
      tGood ξ η hξ ηV hη) ((localizedRefinement tail q p s hs tGood)).hom (n + 1) hnK
  have consume := @exists_original_chart_restriction K inferInstance P hP
    (Localization.Away tGood) inferInstance (QuadraticLocalized.scalar tGood ≫ tail)
    inferInstance inferInstance inferInstance
    (localizedChartSite tail q p tGood) (localizedCoordinateSite tail p tGood) T
    (localizedChartAffine tail q p tGood) (localizedCoordinateAffine tail p tGood)
    (localizedChart tail q p tGood) (localizedChartEtale tail q p tGood)
    (localizedProjection tail p tGood) (localizedProjectionSmooth tail p tGood)
  obtain ⟨Anew, hEq⟩ := consume
    (U := QuadraticLocalized.chart tGood fN j)
    (N := QuadraticLocalized.model tGood fN)
    (D := QuadraticLocalized.boundary tGood fN d)
    (E := QuadraticLocalized.chart tGood fN eChart) (localizedSection tail p s hs tGood)
    (localized_section_law tail p s hs tGood)
    (Scheme.EtaleChart.LocalizedRetainedLift.inclusion q.left p.left (QuadraticLocalized.scalar
      tGood)
      i (j ≫ fN) hi j fN rfl) ft
    (Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
      q.left p.left (QuadraticLocalized.scalar tGood) i (j ≫ fN) hi j fN rfl)
    jt fNt rfl (QuadraticLocalized.boundaryInclusion tGood fN d)
    (QuadraticLocalized.boundary_complement tGood fN j d hd)
    tt hTargett (QuadraticLocalized.cover tGood fN π hπ)
    (QuadraticLocalized.cover_structure tGood fN π hπ)
    (QuadraticLocalized.coordinate tGood fN j aU haU)
    (QuadraticLocalized.coordinate_structure tGood fN j aU haU)
    (QuadraticLocalized.coordinate_cover tGood fN π hπ j aU haU hjπ)
    (QuadraticLocalized.chartInclusion tGood fN eChart)
    (QuadraticLocalized.coordinate tGood fN eChart aE haE)
    (QuadraticLocalized.coordinate_structure tGood fN eChart aE haE)
    (QuadraticLocalized.coordinate_cover tGood fN π hπ eChart aE haE heπ)
    (Scheme.EtaleChart.MarkedBaseChange.chartMark q.left p.left s.left hs
      (QuadraticLocalized.scalar tGood) ξ η hξ ηV hη) ηV
      (Scheme.EtaleChart.MarkedBaseChange.chartMark_coordinate q.left p.left s.left hs
        (QuadraticLocalized.scalar tGood) ξ η hξ ηV hη) B hX i₀ n
      hn hnUnit
  exact ⟨hTargett, Anew, hEq⟩

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.LocalizedRestriction
