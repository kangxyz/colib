/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedConjugateFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedIdentityNullNative

/-! The actual two identity-side seed faces evaluate to their prescribed whole native homotopies. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugateFaces
open CommonReferenceNerve InputIdentitySeedCarrier

variable (X : Scheme.{u})

/-- The target seed face is the fixed positive identity applied to the whole original seed. -/
theorem target_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (target X (r, s)) x =
    Path.toContinuousMap ((InputIdentityPositive.mapHomotopy X).level n
      (r, (InputIdentityPositive.seed X).map n x)) s := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((targetNull X false).symm.trans ((targetUnit X).trans (targetNull X true))) (s, r)) x =
    (InputIdentityPositive.coneHomotopy X).level n
      (r, ((Homotopy.conjugateToZero
        ((unitHomotopy X).postcomp (mappingConeInclusion (InputIdentityPositive.chart X)))
        (InputIdentityPositive.sourceNull X)).path n x s))
  unfold Homotopy.conjugateToZero
  rw [Homotopy.path_trans, Homotopy.path_symm, Homotopy.path_trans]
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedIdentityNullFaces.target_native X false n r _ x
  · rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact InputIdentitySeedIdentityUnitProducts.target_native X n r _ x
    · exact InputIdentitySeedIdentityNullFaces.target_native X true n r _ x

/-- The source seed face is the unchanged seed after the actual source map-id homotopy. -/
theorem source_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (source X (r, s)) x =
    Path.toContinuousMap ((InputIdentityPositive.seed X).map n
      ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x))) s := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((sourceNull X false).symm.trans ((sourceUnit X).trans (sourceNull X true))) (s, r)) x =
    ((Homotopy.conjugateToZero
      ((unitHomotopy X).postcomp (mappingConeInclusion (InputIdentityPositive.chart X)))
      (InputIdentityPositive.sourceNull X)).path n
        ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x)) s)
  unfold Homotopy.conjugateToZero
  rw [Homotopy.path_trans, Homotopy.path_symm, Homotopy.path_trans]
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedIdentityNullFaces.source_native X false n r _ x
  · rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact InputIdentitySeedIdentityUnitProducts.source_native X n r _ x
    · exact InputIdentitySeedIdentityNullFaces.source_native X true n r _ x

/-- The target edge is the fixed whole positive identity precomposed with the original seed. -/
def nativeTarget := Homotopy.precomp (InputIdentityPositive.seed X)
  (InputIdentityPositive.mapHomotopy X)

/-- The terminal edge is the unchanged seed identity track with its original arrow transports. -/
def nativeTerminal := coneSquareIdentityTrack (InputIdentityPositive.seed X)

/-- The source edge is the original source identity postcomposed with the unchanged seed. -/
def nativeSource := (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).postcomp
  (InputIdentityPositive.seed X)

/-- The prescribed full right route has exactly its original two nested time cuts. -/
def nativeRight := ((nativeTarget X).trans (nativeTerminal X)).trans (nativeSource X).symm

/-- Every point of the terminal seed is the unchanged original supported seed. -/
theorem terminal_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (terminalPath X s) x =
    Path.toContinuousMap ((InputIdentityPositive.seed X).map n x) s := by
  have h := target_native X n 1 s x
  rw [Homotopy.at_one] at h
  exact h

/-- The whole actual right surface recovers both native route subdivisions and seed time. -/
theorem right_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (right X (r, s)) x =
    Path.toContinuousMap ((nativeRight X).level n (r, x)) s := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    ((((targetComparison X).trans (Path.Homotopy.refl (terminalPath X))).trans
      (sourceComparison X).symm) (r, s)) x =
    Path.toContinuousMap
      ((((nativeTarget X).trans (nativeTerminal X)).trans (nativeSource X).symm).path n x r) s
  rw [Path.Homotopy.trans_apply, Homotopy.path_trans, Path.trans_apply]
  split
  · rw [Path.Homotopy.trans_apply, Homotopy.path_trans, Path.trans_apply]
    split
    · exact target_native X n _ s x
    · exact terminal_native X n s x
  · exact source_native X n _ s x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugateFaces
