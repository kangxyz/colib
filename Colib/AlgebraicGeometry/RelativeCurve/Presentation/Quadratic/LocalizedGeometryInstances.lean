/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LocalizedGoodGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange

/-! # Structural properties of the same localized model and nested retained open

The nested retained scheme is never replaced by a definitionally equal base-first
pullback. Its actual Cartesian rectangle supplies affineness and relative smoothness.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.QuadraticLocalized
variable {R : Type u} [CommRing R] (t : R)
  {N U : Scheme.{u}} (p : N ⟶ Spec (.of R)) (j : U ⟶ N)

/-- The literal nested retained source is Cartesian over its original structure. -/
theorem retained_structure_isPullback :
    IsPullback (pullback.snd (toOriginal t p) j)
      (chartInclusion t p j ≫ projection t p) (j ≫ p) (scalar t) :=
  (IsPullback.of_hasPullback (toOriginal t p) j).flip.paste_vert
    (IsPullback.of_hasPullback (scalar t) p).flip

/-- Affineness is derived on the actual nested retained pullback. -/
theorem retained_isAffine [IsAffine U] : IsAffine (chart t p j) := by
  have horiginal : IsAffineHom (j ≫ p) :=
    @isAffineHom_of_isAffine U (Spec (.of R)) (j ≫ p) inferInstance inferInstance
  have hnew : IsAffineHom (chartInclusion t p j ≫ projection t p) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (retained_structure_isPullback t p j) horiginal
  exact @isAffine_of_isAffineHom (chart t p j) (Spec (.of (Localization.Away t)))
    (chartInclusion t p j ≫ projection t p) hnew inferInstance

/-- Relative smooth dimension belongs to the original retained map and its actual
base change; it is not imposed as a new hypothesis on the localized source. -/
theorem retained_smoothOfRelativeDimension (d : ℕ)
    [h : SmoothOfRelativeDimension d (j ≫ p)] :
    SmoothOfRelativeDimension d (chartInclusion t p j ≫ projection t p) :=
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
    (retained_structure_isPullback t p j) h

/-- The localized compactification is still proper. -/
theorem model_proper [IsProper p] : IsProper (projection t p) :=
  inferInstanceAs (IsProper (pullback.fst (scalar t) p))

/-- Localization is an open smooth base change, so original normality suffices. -/
theorem model_normal [IsNormal N] : IsNormal (model t p) :=
  quadraticCompactificationBaseChange_isNormal p (algebraMap R (Localization.Away t))

/-- The same original nonempty independent chart, marked over the same etaV,
supplies all structural inputs without assuming global boundary finiteness. -/
theorem marked_geometry
    [IsIntegral N] [IsNormal N] [IsProper p] [IsAffine U]
    [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    {E : Scheme.{u}} (e : E ⟶ N) [IsOpenImmersion e]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ E)
    (ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))
    (hmark : ηV ≫ scalar t = (ξ ≫ e) ≫ p) :
    IsNormal (model t p) ∧ IsIntegral (model t p) ∧ IsProper (projection t p) ∧
    IsAffine (chart t p j) ∧ IsOpenImmersion (chartInclusion t p j) ∧
    SmoothOfRelativeDimension 1 (chartInclusion t p j ≫ projection t p) ∧
    IsOpenImmersion (chartInclusion t p e) ∧ Nonempty (chart t p e) :=
  ⟨model_normal t p, model_integral t p e ξ ηV hmark, model_proper t p,
    retained_isAffine t p j, inferInstance, retained_smoothOfRelativeDimension t p j 1,
    inferInstance, chart_nonempty t p e ξ ηV hmark⟩

/-- The independent-chart mark is actually obtained from the original affine
mark and the original independent principal open. Its base is the same etaV. -/
theorem exists_marked_geometry_from_original
    [IsIntegral N] [IsNormal N] [IsProper p] [IsAffine U]
    [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    {B Ω : Type u} [CommRing B] [Field Ω]
    (i : Spec (.of B) ⟶ N) [IsOpenImmersion i]
    (f : Spec (.of B) ⟶ Spec (.of R)) (hbase : i ≫ p = f)
    (x : Spec (.of Ω) ⟶ Spec (.of B)) (re : B) (hre : re ∉ (x default).asIdeal)
    (ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))
    (hη : ηV ≫ scalar t = x ≫ f) :
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let e := je ≫ i
    ∃ ξ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away re)),
      ξ ≫ je = x ∧ ηV ≫ scalar t = (ξ ≫ e) ≫ p ∧
      IsNormal (model t p) ∧ IsIntegral (model t p) ∧ IsProper (projection t p) ∧
      IsAffine (chart t p j) ∧ IsOpenImmersion (chartInclusion t p j) ∧
      SmoothOfRelativeDimension 1 (chartInclusion t p j ≫ projection t p) ∧
      IsOpenImmersion (chartInclusion t p e) ∧ Nonempty (chart t p e) := by
  let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
  obtain ⟨ξ, hξ⟩ := EtaleChart.MarkedBaseChange.exists_mark_localizationAway x re hre
  have hmark : ηV ≫ scalar t = (ξ ≫ (je ≫ i)) ≫ p := by
    calc
      ηV ≫ scalar t = x ≫ f := hη
      _ = (ξ ≫ je) ≫ f := congrArg (fun z => z ≫ f) hξ.symm
      _ = (ξ ≫ je) ≫ (i ≫ p) := congrArg (fun z => (ξ ≫ je) ≫ z) hbase.symm
      _ = ((ξ ≫ je) ≫ i) ≫ p := (Category.assoc _ _ _).symm
      _ = (ξ ≫ (je ≫ i)) ≫ p := congrArg (fun z => z ≫ p) (Category.assoc _ _ _)
  exact ⟨ξ, hξ, hmark, marked_geometry t p j (je ≫ i) ξ ηV hmark⟩

end AlgebraicGeometry.Scheme.QuadraticLocalized
