/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedConjugateNative
public import Colib.Util.References

/-!
# The actual global raw transition identity square

The six compatible full carrier faces provide the relative extension. Its strict positive
inclusion preserves the prescribed raw input comparison, original seed, and fixed whole
identity. The final compact quotient gives the actual moving-endpoint square.
-/
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedSquare
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedConjugateFaces
variable (X : Scheme.{u})

/-- Both prescribed routes are recovered from the actual six-face carrier boundary. -/
theorem recovers : (surfaces X).boundary.RecoversRoutes
    (positiveTransitionHomotopy (𝟙 X)) (nativeRight X) :=
  (surfaces X).recoversRoutes (positiveTransitionHomotopy (𝟙 X)) (nativeRight X)
    (InputIdentitySeedConjugation.comparison_positiveTransition (𝟙 X)) (right_native X)

/-- The actual complete six-face extension supplies the supported relative identity comparison. -/
def positiveComparison : (positiveTransitionHomotopy (𝟙 X)).RelHomotopy (nativeRight X) :=
  (surfaces X).boundary.relativeComparison
    (positiveTransitionHomotopy (𝟙 X)) (nativeRight X) (recovers X)

/-- The unchanged global target identity edge. -/
def target := Homotopy.precomp (transition X) (InputIdentity.mapHomotopy X)
/-- The literal global identity track on the original transition. -/
def terminal := coneSquareIdentityTrack (transition X)
/-- The original source identity edge, with the fixed global transition. -/
def source := (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).postcomp (transition X)
/-- The complete prescribed global three-side word, with its original association. -/
def right := ((target X).trans (terminal X)).trans (source X).symm

/-- Positive support preserves the complete target identity level, including seed time. -/
theorem target_factor (n : ℕ) :
    (target X).level n = ((nativeTarget X).postcomp
      (parameterLoopingMap (InputIdentityPositive.inclusion X))).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  apply Path.ext
  funext s
  exact (InputIdentityPositive.mapHomotopy_seed X n r s x).symm

/-- The constant terminal route keeps the exact fixed original seed. -/
theorem terminal_factor (n : ℕ) :
    (terminal X).level n = ((nativeTerminal X).postcomp
      (parameterLoopingMap (InputIdentityPositive.inclusion X))).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  exact (congrArg (fun f ↦ f.map n x) (InputIdentityPositive.seed_factor X)).symm

/-- The entire source identity edge keeps the original seed at every source time. -/
theorem source_factor (n : ℕ) :
    (source X).level n = ((nativeSource X).postcomp
      (parameterLoopingMap (InputIdentityPositive.inclusion X))).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  exact (congrArg (fun f ↦ f.map n
    ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x)))
      (InputIdentityPositive.seed_factor X)).symm

/-- The entire right route retains both its original half-time concatenations under inclusion. -/
theorem right_factor (n : ℕ) :
    (right X).level n = ((nativeRight X).postcomp
      (parameterLoopingMap (InputIdentityPositive.inclusion X))).level n := by
  simp only [right, nativeRight, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  apply Homotopy.trans_level_congr
  · exact Homotopy.trans_level_congr _ _ _ _ n (target_factor X n) (terminal_factor X n)
  · exact Homotopy.symm_level_congr _ _ n (source_factor X n)

/-- The relative comparison retains the original raw input transition and fixed three-side word. -/
def comparison : (transitionInputHomotopy (𝟙 X)).RelHomotopy (right X) :=
  ((positiveComparison X).postcomp
    (parameterLoopingMap (InputIdentityPositive.inclusion X))).ofLevels
    (transitionInputHomotopy (𝟙 X)) (right X)
    (fun n ↦ by
      apply ContinuousMap.ext
      rintro ⟨r, x⟩
      apply Path.ext
      funext s
      exact (positiveTransitionHomotopy_factor (𝟙 X) n r s x).symm)
    (right_factor X)

/-- The actual whole transition identity square uses the chosen raw input null and seed. -/
@[colib_tag "COL-1342"]
def square : (transitionInputHomotopy (𝟙 X)).Square
    (coneSquareIdentityTrack (transition X))
    (Homotopy.precomp (transition X) (InputIdentity.mapHomotopy X))
    ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).postcomp (transition X)) :=
  (comparison X).toSquare

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedSquare
