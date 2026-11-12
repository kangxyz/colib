/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenActualRootAuxiliary
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryNoetherian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerExistence
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitEmbedding
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitIntegral
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryFinite
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSameClosedFibre
public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreCartesianRootAuxiliaryFullBoundary

/-! # The same-root supplier on an actual component stage and its actual limit

All local/stage curves, sections, retained opens, full boundaries and cone maps
are the existing objects. Projective embedding and closed-fibre coincidence are
constructed, not supplied as compatibility certificates. The only prescribed
frame is the input stage frame (in the application, its canonical difference frame).
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance actualSameRootResultRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance actualSameRootResultPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance actualSameRootResultUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)



/-- Select the original root and auxiliary pair exactly once, using the canonical
frame of the actual stage kernels, and descend those same inputs on the actual
same-index full-boundary/component cones. The named Result retains all recovery
identities and consumer-normalized final sections, without expanding its body. -/
theorem etaleStageOpen_exists_same_root_consumer_result
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsLocallyNoetherian X.left] [IsProper p]
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsClosedImmersion U.ι]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (hp : IsProjectiveMorphism p)
    {V Z : Scheme.{u}} [IsAffine V]
    (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (d : Z ⟶ U.toScheme) [IsClosedImmersion d]
    [IsFinite (d ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : ↥(etaleLocalRing B X.left hX s))) :
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  letI _hσclosed : IsClosedImmersion σ := by
    let : IsClosedImmersion (σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp σ (U.ι ≫ (etaleCurveStructure X s p).app i)
  letI _hτclosed : IsClosedImmersion τ := by
    let : IsClosedImmersion (τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hτ]
      infer_instance
    exact IsClosedImmersion.of_comp τ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let hdσ : ∀ z : Z, d z ∉ Set.range σ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hσj hz)
  let hdτ : ∀ z : Z, d z ∉ Set.range τ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hτj hz)
  let D := fun a => (etaleStageOpenSection X s p i U σ hσ a).ker
  let E := fun a => (etaleStageOpenSection X s p i U τ hτ a).ker
  let hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U σ hσ v).symm
  let hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U τ hτ v).symm
  let aD := etaleStageOpenSection_boundary_avoids X s p i U σ hσ d hdσ
  let aE := etaleStageOpenSection_boundary_avoids X s p i U τ hτ d hdτ
  letI _hD : ∀ a, IsEffectiveCartierDivisor (D a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U σ hσ j hσj a
  letI _hE : ∀ a, IsEffectiveCartierDivisor (E a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U τ hτ j hτj a
  OriginalRootAuxiliaryFramesConsumerExistence
    B' C b cB cC bLim hb D E hDmap hEmap aD aE a0 n := by
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
  let _hσclosed : IsClosedImmersion σ := by
    let : IsClosedImmersion (σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp σ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let _hτclosed : IsClosedImmersion τ := by
    let : IsClosedImmersion (τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) := by
      rw [hτ]
      infer_instance
    exact IsClosedImmersion.of_comp τ (U.ι ≫ (etaleCurveStructure X s p).app i)
  let hdσ : ∀ z : Z, d z ∉ Set.range σ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hσj hz)
  let hdτ : ∀ z : Z, d z ∉ Set.range τ := by
    intro z hz
    have hdz : d z ∈ Set.range d := ⟨z, rfl⟩
    rw [hd] at hdz
    exact hdz (hτj hz)
  let D := fun a => (etaleStageOpenSection X s p i U σ hσ a).ker
  let E := fun a => (etaleStageOpenSection X s p i U τ hτ a).ker
  let hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U σ hσ v).symm
  let hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a :=
    fun {_ _} v => (etaleStageOpenSection_ker X s p i U τ hτ v).symm
  let aD := etaleStageOpenSection_boundary_avoids X s p i U σ hσ d hdσ
  let aE := etaleStageOpenSection_boundary_avoids X s p i U τ hτ d hdτ
  let _hD : ∀ a, IsEffectiveCartierDivisor (D a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U σ hσ j hσj a
  let _hE : ∀ a, IsEffectiveCartierDivisor (E a) :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U τ hτ j hτj a
  let τStage := differenceSheafBoundaryIso (b.app a0) (D a0) (E a0) (aD a0) (aE a0)
  let _hFP : (differenceSheaf (D a0) (E a0)).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (C.obj a0) _ (isInvertible_differenceSheaf (D a0) (E a0)).toAlgebraicGeometry
  have hRootOutput := etaleStageOpen_exists_actual_root_auxiliary X s p i U B hX x hpre hp
      j d hd σ τ hσ hτ hσj hτj a0 hmark τStage hn0 hn
  exact originalRootAuxiliaryFramesConsumerExistence_of_output
    B' C b cB (etaleStageOpenBoundaryConeIsLimit X s p i U d B hX)
    cC (etaleStageOpenConeIsLimit X s p i U B hX)
    bLim hb D E hDmap hEmap aD aE a0 n hRootOutput

end AlgebraicGeometry.Scheme.SmoothSite
