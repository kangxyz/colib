/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageOriginalTarget
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.RetainedImageMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange

/-! # The original quadratic intersection and independent chart on the same image open

These are the exact pre-localization inputs consumed after the good-neighborhood
producer chooses N/i/π/tGood. Neither the tuple nor either principal open is changed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.QuadraticOriginalImage
variable {B R : Type u} [CommRing B] [CommRing R]
  (F : Polynomial R →+* B) (re r : B) {N : Scheme.{u}}
  (iN : Spec (.of B) ⟶ N) [IsOpenImmersion iN]

abbrev independentInclusion :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
abbrev retainedOpen : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
abbrev imageRetained := (iN ''ᵁ retainedOpen r).toScheme

/-- The actual old chart maps to the image retained source through the native iso. -/
def chartToRetained : quadraticRetainedEtaleChart re r ⟶ imageRetained r iN :=
  pullback.snd (independentInclusion re) (retainedOpen r).ι ≫
    (iN.isoImage (retainedOpen r)).hom

/-- The original chart map, with the exact original parenthesization. -/
abbrev coordinateChart : quadraticRetainedEtaleChart re r ⟶ Spec (.of (Polynomial R)) :=
  pullback.fst (independentInclusion re) (retainedOpen r).ι ≫
    independentInclusion re ≫ Spec.map (CommRingCat.ofHom F)

/-- Original target recovery on the true image retained object. -/
theorem chartToRetained_target {T : Scheme.{u}} (tB : Spec (.of B) ⟶ T) :
    chartToRetained re r iN ≫ retainedImageMap iN (retainedOpen r) tB =
      (pullback.snd (independentInclusion re) (retainedOpen r).ι ≫ (retainedOpen r).ι) ≫ tB := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => pullback.snd (independentInclusion re) (retainedOpen r).ι ≫ z)
      (isoImage_hom_retainedImageMap iN (retainedOpen r) tB)).trans
      (Category.assoc _ _ _).symm)

/-- The actual hi needed by the chart-restriction consumer, not a new hypothesis. -/
theorem chartToRetained_structure (fN : N ⟶ Spec (.of R))
    (hbase : iN ≫ fN = Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))) :
    chartToRetained re r iN ≫ ((iN ''ᵁ retainedOpen r).ι ≫ fN) =
      coordinateChart F re r ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.C : R →+* Polynomial R)) := by
  let je := independentInclusion re
  let jr := (retainedOpen r).ι
  let b := pullback.snd je jr
  let a := pullback.fst je jr
  let c := Spec.map (CommRingCat.ofHom F)
  let P := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have hscalar : c ≫ P = iN ≫ fN := by
    dsimp only [c, P]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hbase.symm
  have himage : chartToRetained re r iN ≫ (iN ''ᵁ retainedOpen r).ι = (b ≫ jr) ≫ iN :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => b ≫ z) (iN.isoImage_hom_ι (retainedOpen r))).trans
        (Category.assoc _ _ _).symm)
  calc
    _ = (chartToRetained re r iN ≫ (iN ''ᵁ retainedOpen r).ι) ≫ fN :=
      (Category.assoc _ _ _).symm
    _ = ((b ≫ jr) ≫ iN) ≫ fN := congrArg (fun z => z ≫ fN) himage
    _ = (b ≫ jr) ≫ (iN ≫ fN) := Category.assoc _ _ _
    _ = (b ≫ jr) ≫ (c ≫ P) := congrArg (fun z => (b ≫ jr) ≫ z) hscalar.symm
    _ = (a ≫ je) ≫ (c ≫ P) := congrArg (fun z => z ≫ (c ≫ P))
      (pullback.condition (f := je) (g := jr)).symm
    _ = (a ≫ je ≫ c) ≫ P := by simp only [Category.assoc]

/-- The separate independent chart retains its original etale coordinate. -/
theorem independentCoordinate_etale
    (he : ((algebraMap B (Localization.Away re)).comp F).Etale) :
    Etale (independentInclusion re ≫ Spec.map (CommRingCat.ofHom F)) := by
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re))) ≫ _)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he

omit [IsOpenImmersion iN] in
/-- The independent chart has the same unchanged tail coordinates. -/
theorem independentCoordinate_structure (fN : N ⟶ Spec (.of R))
    (hbase : iN ≫ fN = Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))) :
    (independentInclusion re ≫ Spec.map (CommRingCat.ofHom F)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      (independentInclusion re ≫ iN) ≫ fN := by
  have hF : Spec.map (CommRingCat.ofHom F) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = iN ≫ fN := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hbase.symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => independentInclusion re ≫ z) hF).trans (Category.assoc _ _ _).symm)

omit [IsOpenImmersion iN] in
/-- Its cover equation uses the same original finite π. -/
theorem independentCoordinate_cover (π : N ⟶ projectiveLine R)
    (hcover : iN ≫ π = Spec.map (CommRingCat.ofHom F) ≫ projectiveLineXChart R) :
    (independentInclusion re ≫ iN) ≫ π =
      (independentInclusion re ≫ Spec.map (CommRingCat.ofHom F)) ≫ projectiveLineXChart R :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => independentInclusion re ≫ z) hcover).trans (Category.assoc _ _ _).symm)

omit [IsOpenImmersion iN] in
/-- The original mark lifts to the independent open, and its tail is the original
eta. This supplies the consumer's zeta rather than assuming it. -/
theorem exists_independent_mark {Ω : Type u} [Field Ω]
    (xE : Spec (.of Ω) ⟶ Spec (.of B)) (hre : re ∉ (xE default).asIdeal)
    (fN : N ⟶ Spec (.of R))
    (hbase : iN ≫ fN = Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))) :
    ∃ ζ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away re)),
      ζ ≫ independentInclusion re = xE ∧
      (ζ ≫ (independentInclusion re ≫ iN)) ≫ fN =
        xE ≫ Spec.map (CommRingCat.ofHom (F.comp Polynomial.C)) := by
  obtain ⟨ζ, hζ⟩ := EtaleChart.MarkedBaseChange.exists_mark_localizationAway xE re hre
  refine ⟨ζ, hζ, ?_⟩
  calc
    _ = ((ζ ≫ independentInclusion re) ≫ iN) ≫ fN :=
      congrArg (fun z => z ≫ fN) (Category.assoc _ _ _).symm
    _ = (xE ≫ iN) ≫ fN := congrArg (fun z => (z ≫ iN) ≫ fN) hζ
    _ = xE ≫ (iN ≫ fN) := Category.assoc _ _ _
    _ = _ := congrArg (fun z => xE ≫ z) hbase

end AlgebraicGeometry.Scheme.QuadraticOriginalImage
