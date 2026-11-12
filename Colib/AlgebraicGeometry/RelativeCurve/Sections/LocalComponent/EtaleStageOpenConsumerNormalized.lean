/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryNoetherian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerStatement
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard

/-! # The actual component system supplied to consumer-normalized descent

This theorem discharges all diagram and ideal-family inputs and returns the
named full consumer-normalized proposition. Its
remaining arguments are exactly the original limit root and auxiliary data of
the existing theorem, and its result retains every original recovery equation.
The initial object `a₀` is an actual object of `Over i`, not silently identified
with the fixed open `U`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance stageNormalizedPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- Apply normalized descent on the two actual same-index component diagrams.
No abstract replacement cone or ideal-compatibility certificate is supplied.
The unapplied tail takes the original root and auxiliary sections, not new choices. -/
theorem etaleStageOpenConsumerNormalized
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))]
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (hdσ : ∀ z : Z, d z ∉ Set.range σ) (hdτ : ∀ z : Z, d z ∉ Set.range τ)
    (a₀ : Over i) :
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
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
  letI _hFP : (differenceSheaf (D a₀) (E a₀)).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (C.obj a₀) _ (isInvertible_differenceSheaf (D a₀) (E a₀)).toAlgebraicGeometry
  let i := a₀
  OriginalRootAuxiliaryFramesConsumerStatement
    B' C b cB cC bLim hb D E hDmap hEmap aD aE i := by
  let I := Over i
  let C := etaleStageOpenDiagram X s p i U
  let B' := etaleStageOpenBoundaryDiagram X s p i U d
  let b := etaleStageOpenBoundaryMap X s p i U d
  let cB := etaleStageOpenBoundaryCone X s p i U d B hX
  let cC := etaleStageOpenCone X s p i U B hX
  let bLim := etaleStageOpenBoundaryLimitMap X s p i U d B hX
  let hb := etaleStageOpenBoundaryCone_square X s p i U d B hX
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
  let _hFP : (differenceSheaf (D a₀) (E a₀)).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (C.obj a₀) _ (isInvertible_differenceSheaf (D a₀) (E a₀)).toAlgebraicGeometry
  exact originalRootAuxiliaryFramesConsumerStatement_of_isLimit
    B' C b cB (etaleStageOpenBoundaryConeIsLimit X s p i U d B hX)
    cC (etaleStageOpenConeIsLimit X s p i U B hX)
    bLim hb D E hDmap hEmap aD aE a₀

end AlgebraicGeometry.Scheme.SmoothSite
