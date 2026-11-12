/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStagePresentation
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LocalizedGoodGeometry
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.RetainedImageMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange

/-! # One good-neighborhood witness supplies the actual localized retained geometry

The finite coefficient field E, original tuple a/c, retained element r and rational
mark xE are all inputs from the same chosen finite stage. Only tGood is extracted
from its already constructed good neighborhood; it is not a new finite-subfield index.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
open AlgebraicGeometry.Scheme
universe u
namespace QuadraticIncidence.InfinityChart

/-- The retained coordinate in the image open is supplied by the actual iso. -/
theorem retained_image_coordinate_structure
    {R : Type u} [CommRing R] {M N : Scheme.{u}}
    (i : M ⟶ N) [IsOpenImmersion i] (W : M.Opens)
    (F : M ⟶ Spec (.of (Polynomial R))) (π : N ⟶ projectiveLine R)
    (hF : F ≫ Spec.map (CommRingCat.ofHom Polynomial.C) =
      i ≫ (π ≫ (projectiveLine R ↘ Spec (.of R)))) :
    retainedImageMap i W F ≫ Spec.map (CommRingCat.ofHom Polynomial.C) =
      (i ''ᵁ W).ι ≫ (π ≫ (projectiveLine R ↘ Spec (.of R))) :=
  retainedImageMap_structure i W F _ _ hF

/-- The native producer's eta is the original tail image of xE. Thus the
localization lift below is for that same eta, not a newly chosen base mark. -/
theorem native_mark_eq_original_tail {A Y Z M Ω : Scheme.{u}}
    (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y)
    (i : A ⟶ M) (f : M ⟶ Y) (hi : i ≫ f = q ≫ p)
    (ξ : Ω ⟶ A) (η : Ω ⟶ Y) (hξ : ξ ≫ q = η ≫ s)
    (x : Ω ⟶ M) (hx : ξ ≫ i = x) : x ≫ f = η := by
  calc
    x ≫ f = (ξ ≫ i) ≫ f := congrArg (fun z => z ≫ f) hx.symm
    _ = ξ ≫ (i ≫ f) := Category.assoc _ _ _
    _ = ξ ≫ (q ≫ p) := congrArg (fun z => ξ ≫ z) hi
    _ = (ξ ≫ q) ≫ p := (Category.assoc _ _ _).symm
    _ = (η ≫ s) ≫ p := congrArg (fun z => z ≫ p) hξ
    _ = η ≫ (s ≫ p) := Category.assoc _ _ _
    _ = η ≫ 𝟙 Y := congrArg (fun z => η ≫ z) hs
    _ = η := Category.comp_id _

/-- Extract the good open exactly once and build its actual finite boundary and
retained polynomial chart. The same xE supplies the lift into Spec(Away tGood). -/
theorem exists_tensorGood_localized_retained
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P : Spec (.of (E ⊗[K] B))) (r : E ⊗[K] B)
    (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[K] B))) (hxE : xE default = P)
    (hgood : HasTensorGoodQuadraticNeighborhood K E B g d I a c P r) :
    let R := MvPolynomial (Fin d) E
    let F := quadraticRelativeCoordinateHom E (E ⊗[K] B)
      (fun j => (1 : E) ⊗ₜ[K] g j) d a c
    let W : (Spec (.of (E ⊗[K] B))).Opens := PrimeSpectrum.basicOpen r
    let η := xE ≫ Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))
    ∃ (N : Scheme.{u}) (i : Spec (.of (E ⊗[K] B)) ⟶ N)
      (π : N ⟶ projectiveLine R) (tGood : R) (hi : IsOpenImmersion i),
      letI := hi
      let p := π ≫ (projectiveLine R ↘ Spec (.of R))
      let U := i ''ᵁ W
      let dN := retainedBoundaryInclusion U
      let aU := retainedImageMap i W (Spec.map (CommRingCat.ofHom F))
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧ IsFinite π ∧ IsProper p ∧
      i ≫ π = Spec.map (CommRingCat.ofHom F) ≫ projectiveLineXChart R ∧
      i ≫ p = Spec.map (CommRingCat.ofHom (F.comp Polynomial.C)) ∧
      IsAffine U.toScheme ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) ∧
      IsFinite ((dN ≫ p) ∣_ PrimeSpectrum.basicOpen tGood) ∧
      IsFinite (QuadraticLocalized.boundaryInclusion tGood p dN ≫
        QuadraticLocalized.projection tGood p) ∧
      aU ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = U.ι ≫ p ∧
      U.ι ≫ π = aU ≫ projectiveLineXChart R ∧
      ∃ (ηV : Spec (.of E) ⟶ Spec (.of (Localization.Away tGood))),
        ηV ≫ QuadraticLocalized.scalar tGood = η := by
  obtain ⟨hz, hzfin, N, D, i, π, b, e, tGood, hi,
    hNint, hNnoeth, hNnormal, hπfin, hπsurj, hproper, hbclosed, hbfin,
    hpb, hesurj, hbcomp, hcover, hbase, htGood, hUaff, hUsmooth,
    hboundaryLocal, hUlocalAff, hZavoid⟩ := hgood
  let := hi
  let R := MvPolynomial (Fin d) E
  let F := quadraticRelativeCoordinateHom E (E ⊗[K] B)
    (fun j => (1 : E) ⊗ₜ[K] g j) d a c
  let W : (Spec (.of (E ⊗[K] B))).Opens := PrimeSpectrum.basicOpen r
  let p := π ≫ (projectiveLine R ↘ Spec (.of R))
  let U := i ''ᵁ W
  let dN := retainedBoundaryInclusion U
  let η := xE ≫ Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))
  have hF : Spec.map (CommRingCat.ofHom F) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = i ≫ p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hbase.symm
  have hηmem : tGood ∉ (η default).asIdeal := by
    change tGood ∉ ((Spec.map (CommRingCat.ofHom (F.comp Polynomial.C))) (xE default)).asIdeal
    rw [hxE]
    exact htGood
  obtain ⟨ηV, hηV⟩ := Scheme.EtaleChart.MarkedBaseChange.exists_mark_localizationAway η tGood hηmem
  have hboundary : IsFinite (QuadraticLocalized.boundaryInclusion tGood p dN ≫
      QuadraticLocalized.projection tGood p) := by
    let : IsFinite ((dN ≫ p) ∣_ PrimeSpectrum.basicOpen tGood) := hboundaryLocal
    exact QuadraticLocalized.boundary_finite tGood p dN
  exact ⟨N, i, π, tGood, hi, hNint, hNnoeth, hNnormal, hπfin, hproper,
    hcover, hbase, hUaff, hUsmooth, hboundaryLocal, hboundary,
    retained_image_coordinate_structure i W _ π hF,
    retainedImageMap_coordinate i W _ π (projectiveLineXChart R) hcover, ηV, hηV⟩

end QuadraticIncidence.InfinityChart
