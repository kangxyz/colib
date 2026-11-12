/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLocalizedInputs
public import Colib.AlgebraicGeometry.Polynomial.RationalTailInductionData
/-! # The selected same-stage lower tail has the actual rational marking

The native chart's chosen lower mark is proved equal to the original tail image,
not silently replaced by another point. The rational-point hypothesis then gives
separability over the actual coefficient field for the same geometric marking.
These are inputs for dimension induction, not an assumed lower isomorphism.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativeCurve
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
universe u
namespace QuadraticIncidence.InfinityChart
/-- The stored lower mark is the original coordinate image of the same rational stage point. -/
theorem sameStageLocalizedInputs_tailMark
    (K F E B : Type u) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [CommRing B] [Algebra F B] [Algebra K B] [IsScalarTower K F B]
    [Algebra.Smooth F B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P0 : Spec (.of (E ⊗[F] B))) (re r : E ⊗[F] B)
    (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[F] B))) (hxE : xE default = P0)
    (hre : re ∉ (xE default).asIdeal)
    (he : ((algebraMap (E ⊗[F] B) (Localization.Away re)).comp
      (quadraticRelativeCoordinateHom E (E ⊗[F] B)
        (fun j => (1 : E) ⊗ₜ[F] g j) d a c)).Etale)
    (hgood : HasTensorGoodQuadraticNeighborhood F E B g d I a c P0 r)
    (hnative : HasQuadraticRetainedNativeChart K E (E ⊗[F] B) hfin hsep d
      (relativeCoordinateAlgHom E (E ⊗[F] B) d
        (fun k => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
          (parameterTuple E σ (d + 1) (prependParameters E d a c) k).val)) xE re r)
    {Ω : Type u} [Field Ω] (φ : E →+* Ω) :
    (sameStageLocalizedInputs K F E B hfin hsep g d I a c P0 re r xE hxE hre he
      hgood hnative φ).η =
      Spec.map (CommRingCat.ofHom φ) ≫ xE ≫
        Spec.map (CommRingCat.ofHom
          ((quadraticRelativeCoordinateHom E (E ⊗[F] B)
            (fun j => (1 : E) ⊗ₜ[F] g j) d a c).comp Polynomial.C)) := by
  classical
  let : Algebra.FormallyEtale K F := Algebra.FormallyEtale.of_isSeparable K F
  let : Algebra.FinitePresentation K F :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth K F := {}
  let : Algebra.Smooth K B := Algebra.Smooth.comp K F B
  let : Module.Finite K E := hfin
  let : Algebra.IsSeparable K E := hsep
  let R := MvPolynomial (Fin d) E
  let coordMap := quadraticRelativeCoordinateHom E (E ⊗[F] B)
    (fun j => (1 : E) ⊗ₜ[F] g j) d a c
  let tail := Spec.map (CommRingCat.ofHom (algebraMap K R))
  let je := QuadraticOriginalImage.independentInclusion re
  let W : (Spec (.of (E ⊗[F] B))).Opens := PrimeSpectrum.basicOpen r
  let qR := QuadraticOriginalImage.coordinateChart coordMap re r
  let pR := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  let hq := Classical.choose hnative
  let H1 := Classical.choose_spec hnative
  let hp := Classical.choose H1
  let H2 := Classical.choose_spec H1
  let : Etale qR := hq
  let : Smooth pR := hp
  let sR := Classical.choose H2
  let H3 := Classical.choose_spec H2
  let hs := Classical.choose H3
  let H4 := Classical.choose_spec H3
  let ηE := Classical.choose H4
  let H5 := Classical.choose_spec H4
  let ξE := Classical.choose H5
  let H6 := Classical.choose_spec H5
  let Y := SmoothSite.mk tail
  let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of R)))
  let hA : IsAffine (quadraticRetainedEtaleChart re r) := quadraticRetainedEtaleChart_isAffine re r
  let hZ : IsAffine (Spec (.of (Polynomial R))) := inferInstance
  let q := @SmoothSite.EtaleChart.chart (Spec (.of K)) Y hY
    (quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial R))) hA hZ pR hp qR hq
  let p := @SmoothSite.EtaleChart.projection (Spec (.of K)) Y hY
    (Spec (.of (Polynomial R))) hZ pR hp
  let s := @SmoothSite.EtaleChart.sectionMap (Spec (.of K)) Y hY
    (Spec (.of (Polynomial R))) hZ pR hp sR hs
  have hηE : xE ≫ Spec.map (CommRingCat.ofHom (coordMap.comp Polynomial.C)) = ηE :=
    native_mark_eq_original_tail qR pR sR hs (pullback.snd je W.ι ≫ W.ι)
      (Spec.map (CommRingCat.ofHom (coordMap.comp Polynomial.C)))
      (intersection_original_tail coordMap re r) ξE ηE H6.2.1 xE H6.2.2
  change Spec.map (CommRingCat.ofHom φ) ≫ ηE = _
  exact congrArg (fun z => Spec.map (CommRingCat.ofHom φ) ≫ z) hηE.symm


/-- The selected lower marking has separable native residue over its actual coefficient field. -/
theorem sameStageLocalizedInputs_tailResidue_separable
    (K F E B : Type u) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [CommRing B] [Algebra F B] [Algebra K B] [IsScalarTower K F B]
    [Algebra.Smooth F B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P0 : Spec (.of (E ⊗[F] B))) (re r : E ⊗[F] B)
    (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[F] B))) (hxE : xE default = P0)
    (hre : re ∉ (xE default).asIdeal)
    (he : ((algebraMap (E ⊗[F] B) (Localization.Away re)).comp
      (quadraticRelativeCoordinateHom E (E ⊗[F] B)
        (fun j => (1 : E) ⊗ₜ[F] g j) d a c)).Etale)
    (hgood : HasTensorGoodQuadraticNeighborhood F E B g d I a c P0 r)
    (hnative : HasQuadraticRetainedNativeChart K E (E ⊗[F] B) hfin hsep d
      (relativeCoordinateAlgHom E (E ⊗[F] B) d
        (fun k => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
          (parameterTuple E σ (d + 1) (prependParameters E d a c) k).val)) xE re r)
    {Ω : Type u} [Field Ω] (φ : E →+* Ω)
    (hxRat : xE ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[F] B))) = 𝟙 _) :
    let η := (sameStageLocalizedInputs K F E B hfin hsep g d I a c P0 re r xE hxE hre he
      hgood hnative φ).η
    letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))))
      (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable E ((Spec (.of (MvPolynomial (Fin d) E))).residueField
      (η (IsLocalRing.closedPoint Ω))) := by
  dsimp only
  rw [sameStageLocalizedInputs_tailMark K F E B hfin hsep g d I a c P0 re r xE
    hxE hre he hgood hnative φ]
  exact Scheme.isSeparable_polynomialTail_extendedMark_residue E Ω (E ⊗[F] B) φ d
    (relativeCoordinateAlgHom E (E ⊗[F] B) d
      (fun k => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
        (parameterTuple E σ (d + 1) (prependParameters E d a c) k).val)) xE hxRat

end QuadraticIncidence.InfinityChart
