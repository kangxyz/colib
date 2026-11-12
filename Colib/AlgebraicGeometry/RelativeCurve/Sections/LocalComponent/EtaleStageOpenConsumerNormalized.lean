/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryNoetherian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerNormalized
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard

/-! # The actual component system supplied to consumer-normalized descent

This partial application discharges all diagram and ideal-family inputs. Its
remaining arguments are exactly the original limit root and auxiliary data of
the existing theorem, and its result retains every original recovery equation.
The initial object `a₀` is an actual object of `Over i`, not silently identified
with the fixed open `U`. This draft has not been compiled.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

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
    (a₀ : Over i) : _ :=
  letI : ∀ a, IsEffectiveCartierDivisor
      (etaleStageOpenSection X s p i U σ hσ a).ker :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U σ hσ j hσj a
  letI : ∀ a, IsEffectiveCartierDivisor
      (etaleStageOpenSection X s p i U τ hτ a).ker :=
    fun a => etaleStageOpenSection_isEffectiveCartierDivisor X s p i U τ hτ j hτj a
  letI : (differenceSheaf (etaleStageOpenSection X s p i U σ hσ a₀).ker
      (etaleStageOpenSection X s p i U τ hτ a₀).ker).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      ((etaleStageOpenDiagram X s p i U).obj a₀) _
      (isInvertible_differenceSheaf
        (etaleStageOpenSection X s p i U σ hσ a₀).ker
        (etaleStageOpenSection X s p i U τ hτ a₀).ker).toAlgebraicGeometry
  exists_original_root_auxiliaryFrames_consumer_normalized_of_isLimit
    (etaleStageOpenBoundaryDiagram X s p i U d)
    (etaleStageOpenDiagram X s p i U)
    (etaleStageOpenBoundaryMap X s p i U d)
    (etaleStageOpenBoundaryCone X s p i U d B hX)
    (etaleStageOpenBoundaryConeIsLimit X s p i U d B hX)
    (etaleStageOpenCone X s p i U B hX)
    (etaleStageOpenConeIsLimit X s p i U B hX)
    (etaleStageOpenBoundaryLimitMap X s p i U d B hX)
    (etaleStageOpenBoundaryCone_square X s p i U d B hX)
    (fun a => (etaleStageOpenSection X s p i U σ hσ a).ker)
    (fun a => (etaleStageOpenSection X s p i U τ hτ a).ker)
    (fun {_ _} v => (etaleStageOpenSection_ker X s p i U σ hσ v).symm)
    (fun {_ _} v => (etaleStageOpenSection_ker X s p i U τ hτ v).symm)
    (etaleStageOpenSection_boundary_avoids X s p i U σ hσ d hdσ)
    (etaleStageOpenSection_boundary_avoids X s p i U τ hτ d hdτ)
    a₀

end AlgebraicGeometry.Scheme.SmoothSite
