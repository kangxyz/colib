/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLocalizedConsumerGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageRetainedNativeChart

/-! # Store one finite-stage geometry package over the original ground field

The typed data record stores the original choices once. The coefficient field
F may differ from the transfer ground field K. The finite-stage constructor
keeps the actual original target and its K-structure; it does not assert the
restriction consumer or the dimension-induction conclusion.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativeCurve
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
universe u
namespace QuadraticIncidence.InfinityChart

/-- The literal intersection has the original tail map, independently of any
compactification or image-open transport. -/
theorem intersection_original_tail {B R : Type u} [CommRing B] [CommRing R]
    (F : Polynomial R →+* B) (re r : B) :
    let je := QuadraticOriginalImage.independentInclusion re
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    (pullback.snd je jr ≫ jr) ≫ Spec.map (CommRingCat.ofHom (F.comp Polynomial.C)) =
      QuadraticOriginalImage.coordinateChart F re r ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  intro je jr
  let c := Spec.map (CommRingCat.ofHom F)
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have hc : Spec.map (CommRingCat.ofHom (F.comp Polynomial.C)) = c ≫ p := by
    dsimp only [c, p]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  calc
    _ = (pullback.snd je jr ≫ jr) ≫ (c ≫ p) := congrArg (fun z => (pullback.snd je jr ≫ jr) ≫ z) hc
    _ = (pullback.fst je jr ≫ je) ≫ (c ≫ p) :=
      congrArg (fun z => z ≫ (c ≫ p)) (pullback.condition (f := je) (g := jr)).symm
    _ = _ := by
      dsimp only [QuadraticOriginalImage.coordinateChart,
        QuadraticOriginalImage.retainedOpen, je, jr, c, p]
      simp only [Category.assoc]

/-- The actual geometry and markings selected by one finite-stage construction. -/
structure SameStageLocalizedInputs (K Ω : Type u) [Field K] [Field Ω] where
  R : Type u
  [ring : CommRing R]
  tail : Spec (.of R) ⟶ Spec (.of K)
  [tailSmooth : Smooth tail]
  [tailSeparated : IsSeparated tail]
  [tailQuasiCompact : QuasiCompact tail]
  A : SmoothSite (Spec (.of K))
  Z : SmoothSite (Spec (.of K))
  T : SmoothSite (Spec (.of K))
  [affineA : IsAffine A.left]
  [affineZ : IsAffine Z.left]
  q : A ⟶ Z
  [etaleQ : Etale q.left]
  p : Z ⟶ SmoothSite.mk tail
  [smoothP : Smooth p.left]
  s : SmoothSite.mk tail ⟶ Z
  hs : s.left ≫ p.left = 𝟙 _
  tGood : R
  ξ : Spec (.of Ω) ⟶ A.left
  η : Spec (.of Ω) ⟶ Spec (.of R)
  hξ : ξ ≫ q.left = η ≫ s.left
  ηV : Spec (.of Ω) ⟶ Spec (.of (Localization.Away tGood))
  hη : ηV ≫ QuadraticLocalized.scalar tGood = η
  U : Scheme.{u}
  N : Scheme.{u}
  D : Scheme.{u}
  E : Scheme.{u}
  [affineU : IsAffine U]
  [integralN : IsIntegral N]
  [normalN : IsNormal N]
  j : U ⟶ N
  [openJ : IsOpenImmersion j]
  fN : N ⟶ Spec (.of R)
  [properFN : IsProper fN]
  [smoothU : SmoothOfRelativeDimension 1 (j ≫ fN)]
  i : A.left ⟶ U
  hi : i ≫ (j ≫ fN) = q.left ≫ p.left
  d : D ⟶ N
  [closedD : IsClosedImmersion d]
  [finiteLocal : IsFinite ((d ≫ fN) ∣_ PrimeSpectrum.basicOpen tGood)]
  hd : Set.range d = (Set.range j)ᶜ
  targetU : U ⟶ T.left
  hTarget : targetU ≫ T.hom = (j ≫ fN) ≫ tail
  π : N ⟶ projectiveLine R
  [finitePi : IsFinite π]
  hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = fN
  aU : U ⟶ Spec (.of (Polynomial R))
  haU : aU ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = j ≫ fN
  hjπ : j ≫ π = aU ≫ projectiveLineXChart R
  eChart : E ⟶ N
  [openChart : IsOpenImmersion eChart]
  aE : E ⟶ Spec (.of (Polynomial R))
  [etaleAE : Etale aE]
  haE : aE ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = eChart ≫ fN
  heπ : eChart ≫ π = aE ≫ projectiveLineXChart R
  ζ : Spec (.of Ω) ⟶ E
  hζ : (ζ ≫ eChart) ≫ fN = η

attribute [local instance] SameStageLocalizedInputs.ring
  SameStageLocalizedInputs.tailSmooth SameStageLocalizedInputs.tailSeparated
  SameStageLocalizedInputs.tailQuasiCompact SameStageLocalizedInputs.affineA
  SameStageLocalizedInputs.affineZ SameStageLocalizedInputs.etaleQ
  SameStageLocalizedInputs.smoothP SameStageLocalizedInputs.affineU
  SameStageLocalizedInputs.integralN SameStageLocalizedInputs.normalN
  SameStageLocalizedInputs.openJ SameStageLocalizedInputs.properFN
  SameStageLocalizedInputs.smoothU SameStageLocalizedInputs.closedD
  SameStageLocalizedInputs.finiteLocal SameStageLocalizedInputs.finitePi
  SameStageLocalizedInputs.openChart SameStageLocalizedInputs.etaleAE

open SmoothSite

/-- Select the native chart and good geometry once, retaining every actual map.
The coefficient field F need not be the transfer ground field K. The hypotheses
hfin and hsep concern E/K and can be supplied by transitivity from E/F and F/K.
The original target here is B as a K-scheme; its further map to an earlier target
is not part of this theorem. -/
def sameStageLocalizedInputs
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
    {Ω : Type u} [Field Ω] (φ : E →+* Ω) : SameStageLocalizedInputs K Ω := by
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
  let HG := exists_sameStage_localized_consumer_geometry F E B g d I a c P0 r
    xE hxE re hre he hgood
  let N := Classical.choose HG
  let G1 := Classical.choose_spec HG
  let iN := Classical.choose G1
  let G2 := Classical.choose_spec G1
  let π := Classical.choose G2
  let G3 := Classical.choose_spec G2
  let tGood := Classical.choose G3
  let G4 := Classical.choose_spec G3
  let hOpen := Classical.choose G4
  let G5 := Classical.choose_spec G4
  let : IsOpenImmersion iN := hOpen
  let U := iN ''ᵁ W
  let fN := π ≫ (projectiveLine R ↘ Spec (.of R))
  let : IsIntegral N := G5.1
  let : IsNormal N := G5.2.2.1
  let : IsFinite π := G5.2.2.2.1
  let : IsProper fN := G5.2.2.2.2.1
  let G6 := G5.2.2.2.2.2
  let : IsAffine U.toScheme := G6.2.2.1
  let : SmoothOfRelativeDimension 1 (U.ι ≫ fN) := G6.2.2.2.1
  let : IsFinite ((retainedBoundaryInclusion U ≫ fN) ∣_ PrimeSpectrum.basicOpen tGood) :=
    G6.2.2.2.2.1
  let G7 := G6.2.2.2.2.2
  let ηVE := Classical.choose G7.2.2.2
  let G8 := Classical.choose_spec G7.2.2.2
  let ζE := Classical.choose G8.2.2.2.2.2
  let G9 := Classical.choose_spec G8.2.2.2.2.2
  let β := Spec.map (CommRingCat.ofHom φ)
  let ξ := β ≫ ξE
  let η := β ≫ ηE
  let ηV := β ≫ ηVE
  have hξ : ξ ≫ q.left = η ≫ s.left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => β ≫ z) H6.2.1).trans (Category.assoc _ _ _).symm)
  have hη : ηV ≫ QuadraticLocalized.scalar tGood = η :=
    (Category.assoc _ _ _).trans (congrArg (fun z => β ≫ z) (G8.1.trans hηE))
  let eChart := je ≫ iN
  let aE := je ≫ Spec.map (CommRingCat.ofHom coordMap)
  let : Etale aE := G8.2.2.1
  let ζ := β ≫ ζE
  have hζ : (ζ ≫ eChart) ≫ fN = η := by
    calc
      (ζ ≫ eChart) ≫ fN = (β ≫ (ζE ≫ eChart)) ≫ fN :=
        congrArg (fun z => z ≫ fN) (Category.assoc _ _ _)
      _ = β ≫ ((ζE ≫ eChart) ≫ fN) := Category.assoc _ _ _
      _ = η := congrArg (fun z => β ≫ z) (G9.2.1.trans hηE)
  let iU := QuadraticOriginalImage.chartToRetained re r iN
  let targetU := retainedImageMap iN W (finiteStageOriginalTarget F E B)
  let T := originalAffineTargetSite K B
  let : IsAffine (@SmoothSite.EtaleChart.chartSite (Spec (.of K)) Y hY
    (quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial R)))
    hA hZ pR hp qR hq).left := hA
  let : IsAffine (@SmoothSite.EtaleChart.coordinateSite (Spec (.of K)) Y hY
    (Spec (.of (Polynomial R))) hZ pR hp).left := hZ
  let : Etale q.left := hq
  let : Smooth p.left := hp
  let toGround := Spec.map (CommRingCat.ofHom (algebraMap K F))
  let tailF := Spec.map (CommRingCat.ofHom (algebraMap F R))
  have hScalar (A₁ : Type u) [CommRing A₁] [Algebra F A₁] [Algebra K A₁]
      [IsScalarTower K F A₁] :
      Spec.map (CommRingCat.ofHom (algebraMap F A₁)) ≫ toGround =
        Spec.map (CommRingCat.ofHom (algebraMap K A₁)) := by
    dsimp only [toGround]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K F A₁]
  have hTargetF : targetU ≫ Spec.map (CommRingCat.ofHom (algebraMap F B)) =
      (U.ι ≫ fN) ≫ tailF := G9.2.2.2.2.2.trans (Category.assoc _ _ _).symm
  have hTarget : targetU ≫ T.hom = (U.ι ≫ fN) ≫ tail := by
    calc
      _ = targetU ≫ (Spec.map (CommRingCat.ofHom (algebraMap F B)) ≫ toGround) :=
        congrArg (fun z => targetU ≫ z) (hScalar B).symm
      _ = (targetU ≫ Spec.map (CommRingCat.ofHom (algebraMap F B))) ≫ toGround :=
        (Category.assoc _ _ _).symm
      _ = ((U.ι ≫ fN) ≫ tailF) ≫ toGround := congrArg (fun z => z ≫ toGround) hTargetF
      _ = (U.ι ≫ fN) ≫ (tailF ≫ toGround) := Category.assoc _ _ _
      _ = _ := congrArg (fun z => (U.ι ≫ fN) ≫ z) (hScalar R)
  have hd : Set.range (retainedBoundaryInclusion U) = (Set.range U.ι)ᶜ := by
    rw [range_retainedBoundaryInclusion, Scheme.Opens.range_ι]
  exact {
    R := R
    ring := inferInstance
    tail := tail
    tailSmooth := inferInstance
    tailSeparated := inferInstance
    tailQuasiCompact := inferInstance
    A := @SmoothSite.EtaleChart.chartSite (Spec (.of K)) Y hY
      (quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial R))) hA hZ pR hp qR hq
    Z := @SmoothSite.EtaleChart.coordinateSite (Spec (.of K)) Y hY
      (Spec (.of (Polynomial R))) hZ pR hp
    T := T
    affineA := hA
    affineZ := hZ
    q := q
    etaleQ := hq
    p := p
    smoothP := hp
    s := s
    hs := hs
    tGood := tGood
    ξ := ξ
    η := η
    hξ := hξ
    ηV := ηV
    hη := hη
    U := U.toScheme
    N := N
    D := retainedBoundary U
    E := Spec (.of (Localization.Away re))
    affineU := G6.2.2.1
    integralN := G5.1
    normalN := G5.2.2.1
    j := U.ι
    openJ := inferInstance
    fN := fN
    properFN := G5.2.2.2.2.1
    smoothU := G6.2.2.2.1
    i := iU
    hi := G8.2.1
    d := retainedBoundaryInclusion U
    closedD := inferInstance
    finiteLocal := G6.2.2.2.2.1
    hd := hd
    targetU := targetU
    hTarget := hTarget
    π := π
    finitePi := G5.2.2.2.1
    hπ := rfl
    aU := retainedImageMap iN W (Spec.map (CommRingCat.ofHom coordMap))
    haU := G7.2.1
    hjπ := G7.2.2.1
    eChart := eChart
    openChart := inferInstance
    aE := aE
    etaleAE := G8.2.2.1
    haE := G8.2.2.2.1
    heπ := G8.2.2.2.2.1
    ζ := ζ
    hζ := hζ }

end QuadraticIncidence.InfinityChart
