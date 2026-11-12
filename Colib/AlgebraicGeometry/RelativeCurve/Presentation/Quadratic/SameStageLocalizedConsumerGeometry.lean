/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.TensorGoodLocalizedRetained
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.OriginalChartImageInputs
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LocalizedGeometryInstances
public import Colib.RingTheory.Bertini.RelativePolynomialCoordinateAlgebra

/-! # One same-stage good witness supplies the actual localized consumer geometry

No native section or chart is selected again. The chart is the same literal
intersection, and the independent mark is constructed from the same original xE.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.Scheme
universe u
namespace QuadraticIncidence.InfinityChart

/-- The actual target on the image retained open remains over the original K.
Its scalar equation is derived from the unchanged E-algebra coordinate map. -/
theorem retainedImageOriginalTarget_over_ground
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] (d : ℕ)
    (F : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] (E ⊗[K] B))
    {N : Scheme.{u}} (i : Spec (.of (E ⊗[K] B)) ⟶ N) [IsOpenImmersion i]
    (W : (Spec (.of (E ⊗[K] B))).Opens)
    (p : N ⟶ Spec (.of (MvPolynomial (Fin d) E)))
    (hbase : i ≫ p = Spec.map (CommRingCat.ofHom (F.toRingHom.comp Polynomial.C))) :
    retainedImageMap i W (finiteStageOriginalTarget K E B) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      (i ''ᵁ W).ι ≫ p ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))) := by
  have hcoord : Spec.map (CommRingCat.ofHom F.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : MvPolynomial (Fin d) E →+*
        Polynomial (MvPolynomial (Fin d) E))) = i ≫ p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hbase.symm
  apply retainedImageMap_structure i W (finiteStageOriginalTarget K E B)
    (Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
  exact (finiteStageOriginalTarget_coordinate_base K E B d F).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial (Fin d) E)))) hcoord).trans (Category.assoc _ _ _)))

theorem exists_sameStage_localized_consumer_geometry
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P : Spec (.of (E ⊗[K] B))) (r : E ⊗[K] B)
    (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[K] B))) (hxE : xE default = P)
    (re : E ⊗[K] B) (hre : re ∉ (xE default).asIdeal)
    (he : ((algebraMap (E ⊗[K] B) (Localization.Away re)).comp
      (quadraticRelativeCoordinateHom E (E ⊗[K] B)
        (fun j => (1 : E) ⊗ₜ[K] g j) d a c)).Etale)
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
        ηV ≫ QuadraticLocalized.scalar tGood = η ∧
        let je := QuadraticOriginalImage.independentInclusion re
        let eChart := je ≫ i
        let aE := je ≫ Spec.map (CommRingCat.ofHom F)
        let iU := QuadraticOriginalImage.chartToRetained re r i
        let q := QuadraticOriginalImage.coordinateChart F re r
        let pLine := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
        iU ≫ (U.ι ≫ p) = q ≫ pLine ∧
        Etale aE ∧ aE ≫ pLine = eChart ≫ p ∧
        eChart ≫ π = aE ≫ projectiveLineXChart R ∧
        ∃ ζ : Spec (.of E) ⟶ Spec (.of (Localization.Away re)),
          ζ ≫ je = xE ∧ (ζ ≫ eChart) ≫ p = η ∧
          IsIntegral (QuadraticLocalized.model tGood p) ∧
          Nonempty (QuadraticLocalized.chart tGood p eChart) ∧
          let targetU := retainedImageMap i W (finiteStageOriginalTarget K E B)
          iU ≫ targetU =
            (pullback.snd je W.ι ≫ W.ι) ≫ finiteStageOriginalTarget K E B ∧
          targetU ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
            U.ι ≫ p ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  obtain ⟨N, i, π, tGood, hi, hNint, hNnoeth, hNnormal, hπfin, hproper,
    hcover, hbase, hUaff, hUsmooth, hboundaryLocal, hboundary, haU, hjπ, ηV, hηV⟩ :=
    exists_tensorGood_localized_retained K E B g d I a c P r xE hxE hgood
  let := hi
  let := hNint
  let R := MvPolynomial (Fin d) E
  let F := quadraticRelativeCoordinateHom E (E ⊗[K] B)
    (fun j => (1 : E) ⊗ₜ[K] g j) d a c
  let p := π ≫ (projectiveLine R ↘ Spec (.of R))
  let je := QuadraticOriginalImage.independentInclusion re
  let eChart := je ≫ i
  obtain ⟨ζ, hζ, hζbase⟩ :=
    QuadraticOriginalImage.exists_independent_mark F re i xE hre p hbase
  have hmark : ηV ≫ QuadraticLocalized.scalar tGood = (ζ ≫ eChart) ≫ p :=
    hηV.trans hζbase.symm
  exact ⟨N, i, π, tGood, hi, hNint, hNnoeth, hNnormal, hπfin, hproper,
    hcover, hbase, hUaff, hUsmooth, hboundaryLocal, hboundary, haU, hjπ, ηV, hηV,
    QuadraticOriginalImage.chartToRetained_structure F re r i p hbase,
    QuadraticOriginalImage.independentCoordinate_etale F re he,
    QuadraticOriginalImage.independentCoordinate_structure F re i p hbase,
    QuadraticOriginalImage.independentCoordinate_cover F re i π hcover,
    ζ, hζ, hζbase, QuadraticLocalized.model_integral tGood p eChart ζ ηV hmark,
    QuadraticLocalized.chart_nonempty tGood p eChart ζ ηV hmark,
    QuadraticOriginalImage.chartToRetained_target re r i (finiteStageOriginalTarget K E B),
    retainedImageOriginalTarget_over_ground K E B d
      (QuadraticIncidence.relativeCoordinateAlgHom E (E ⊗[K] B) d
        (fun k => aeval (fun j => (1 : E) ⊗ₜ[K] g j)
          (parameterTuple E σ (d + 1) (prependParameters E d a c) k).val))
      i (PrimeSpectrum.basicOpen r) p hbase⟩

end QuadraticIncidence.InfinityChart
