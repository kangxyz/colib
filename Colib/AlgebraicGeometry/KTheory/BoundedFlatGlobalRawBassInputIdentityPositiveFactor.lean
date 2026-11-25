/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveSupport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityMap
public import Colib.Topology.Prespectrum.HomotopySquareMappedSupport
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyOperationEvaluation

/-!
# Exact positive support of the fixed global raw identity homotopy

The original plus unit square supplies a positive-cone identity. Its strict image equals the
already fixed whole-cone identity on every positive-cone point. The proof retains the complete
moving-null boundary, its initial-pause contraction, and the original square lift. Consequently
the fixed map identity on the original transition requires only this actual positive support.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
open scoped Topology unitInterval
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositive
variable (X : Scheme.{u})

/-- The original positive unit square gives the complete positive-cone moving-null square. -/
def nullSquare :=
  coneSquareIdentityMovingNullSquare (chart X) (plusSquareHomotopy (𝟙 X))
    (InputIdentity.polynomialHomotopy X) (InputIdentity.laurentHomotopy X)
    (InputIdentity.plusSquare X)

/-- The positive identity retains the initial-pause correction of the original cone map. -/
def coneHomotopy : Homotopy (coneMap (𝟙 X)) (𝟙 (mappingCone (chart X))) :=
  coneSquareIdentityHomotopyOfSquare (chart X) (plusSquareHomotopy (𝟙 X))
    (InputIdentity.polynomialHomotopy X) (InputIdentity.laurentHomotopy X)
    (InputIdentity.plusSquare X)

/-- The identity correction itself preserves every mapped cylinder point and both times. -/
theorem nullCorrection_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace)).space n) :
    (inclusion X).map n ((coneSquareIdentityNullComparison (chart X)).level n (r, (s, x))) =
      (coneSquareIdentityNullComparison (comparison X)).level n
        (r, (s, (HomotopyPushout.inl
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n x)) := by
  change (inclusion X).map n
    ((Homotopy.RelHomotopy.reflTrans (mappingConeHomotopy (chart X))).level n (r, (s, x))) =
    (Homotopy.RelHomotopy.reflTrans (mappingConeHomotopy (comparison X))).level n
      (r, (s, (HomotopyPushout.inl
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n x))
  rw [Homotopy.RelHomotopy.reflTrans_apply_path, Homotopy.RelHomotopy.reflTrans_apply_path]
  rfl

/-- The complete positive null square is the fixed whole square on its original inl face. -/
theorem nullSquare_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace)).space n) :
    (inclusion X).map n ((nullSquare X).level n (r, (s, x))) =
      (InputIdentity.comparisonConeNullSquare X).level n
        (r, (s, (HomotopyPushout.inl
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n x)) := by
  unfold nullSquare InputIdentity.comparisonConeNullSquare coneSquareIdentityMovingNullSquare
  apply Homotopy.RelHomotopy.toSquare_mapped_points
  intro r' s'
  apply Homotopy.RelHomotopy.trans_mapped_points
  · intro r'' s''
    apply Homotopy.Square.toBoundary_mapped_points
    intro r''' s'''
    unfold coneSquareNullMovingSquare
    apply Homotopy.Square.pastePaths_mapped_points
    · intro t w
      rfl
    · intro t w
      rfl
  · intro r'' s''
    apply Homotopy.RelHomotopy.hcomp_mapped_points
    · intro r''' s'''
      apply Homotopy.RelHomotopy.hcomp_mapped_points
      · intro _ _
        rfl
      · intro t w
        exact nullCorrection_factor X n t w x
    · intro _ _
      rfl

/-- The fixed whole identity agrees with this positive identity on every supported cone point. -/
theorem coneHomotopy_factor (n : ℕ) (r : unitInterval)
    (x : (mappingCone (chart X)).space n) :
    (inclusion X).map n ((coneHomotopy X).level n (r, x)) =
      (InputIdentity.coneHomotopy X).level n (r, (inclusion X).map n x) := by
  have h : (coneHomotopy X).at r ≫ inclusion X =
      inclusion X ≫ (InputIdentity.coneHomotopy X).at r := by
    apply mappingCone_hom_ext
    · apply Topology.LoopPrespectrum.Hom.ext
      funext k
      apply ContinuousMap.ext
      intro y
      rfl
    · intro k s y
      exact nullSquare_factor X k r s y
  exact congrArg (fun k ↦ k.map n x) h

/-- Parameter looping preserves the exact positive identity at its independent loop time. -/
def mapHomotopy : Homotopy (parameterLoopingMap (coneMap (𝟙 X)))
    (𝟙 (parameterLooping (mappingCone (chart X)))) :=
  (coneHomotopy X).parameterLooping.cast rfl
    (parameterLoopingFunctor.map_id (mappingCone (chart X)))

/-- Every loop is preserved under the fixed whole identity, not only the seed. -/
theorem mapHomotopy_factor (n : ℕ) (r s : unitInterval)
    (γ : (parameterLooping (mappingCone (chart X))).space n) :
    (inclusion X).map n (Path.toContinuousMap ((mapHomotopy X).level n (r, γ)) s) =
      Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n
        (r, (parameterLoopingMap (inclusion X)).map n γ)) s :=
  coneHomotopy_factor X n r (Path.toContinuousMap γ s)

/-- The unchanged original transition sees exactly the constructed positive identity face. -/
theorem mapHomotopy_seed (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    (inclusion X).map n
      (Path.toContinuousMap ((mapHomotopy X).level n (r, (seed X).map n x)) s) =
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n
      (r, (transition X).map n x)) s := by
  have h := mapHomotopy_factor X n r s ((seed X).map n x)
  have hs := congrArg (fun k ↦ k.map n x) (seed_factor X)
  exact h.trans (congrArg (fun y ↦
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n (r, y)) s) hs)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositive
