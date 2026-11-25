/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputUnit
public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompConjugation
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Exact positive-support factor of the chosen initial-seed scheme-arrow homotopy

The original unit/null recipe is performed in the positive cone, retaining its original
geometric pastings, associators, cancellations and independent parameters. Its whole image
under the strict positive inclusion is the already chosen initial-seed scheme-arrow homotopy.
The higher mixed C0/J0/C1 projection pasting remains a separate obligation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass
namespace InputIdentityPositiveSeed
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original old unit loop after Laurent scheme-arrow change and target cone inclusion. -/
def oldUnit := (InputUnit.oldUnit g).postcomp
  (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The original new unit loop after base scheme-arrow change and target cone inclusion. -/
def newUnit := (InputUnit.newUnit g).postcomp
  (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The proved unit pasting retains every original coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit g).trans (InputIdentityPositiveNull.laurentMovement g)).RelHomotopy
      ((InputIdentityPositiveNull.laurentMovement g).trans (newUnit g)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit,
    InputIdentityPositiveNull.laurentMovement] using
    (laurentUnitPasting g).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- Cancel the proved actual moving Laurent track inside the two original null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (InputIdentityPositiveNull.laurentMovement g)
    (oldUnit g) (newUnit g) (InputIdentityPositiveNull.originalOldNull g)
    (InputIdentityPositiveNull.originalNewNull g)
    (unitPasting g) (InputIdentityPositiveNull.originalNullComparison g)

/-- The source based-loop map is the literal original transition followed by the actual step map. -/
lemma source_eq :
    ((oldUnit g).conjugateToZero
      (InputIdentityPositiveNull.originalOldNull g)).zeroLoopMap =
      InputIdentityPositive.seed Y ≫
        parameterLoopingMap (InputIdentityPositive.coneMap g) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit g).conjugateToZero
    (InputIdentityPositiveNull.originalOldNull g)).level n (s, x) =
    ((((unitHomotopy Y).postcomp
      (mappingConeInclusion
        (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app Y)))).conjugateToZero
        (InputIdentityPositive.sourceNull Y)).postcomp
          (InputIdentityPositive.coneMap g)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target based-loop map is the actual base map followed by the supported transition. -/
lemma target_eq :
    ((newUnit g).conjugateToZero
      (InputIdentityPositiveNull.originalNewNull g)).zeroLoopMap =
      boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        InputIdentityPositive.seed X := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit g).conjugateToZero
    (InputIdentityPositiveNull.originalNewNull g)).level n (s, x) =
    (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
      (((unitHomotopy X).postcomp
        (mappingConeInclusion
        (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))).conjugateToZero
          (InputIdentityPositive.sourceNull X))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end InputIdentityPositiveSeed
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every actual scheme arrow gives a whole homotopy of the supported Bass transitions. -/
def positiveTransitionHomotopy :
    Homotopy (InputIdentityPositive.seed Y ≫
      parameterLoopingMap (InputIdentityPositive.coneMap g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        InputIdentityPositive.seed X) :=
  (InputIdentityPositiveSeed.conjugateComparison g).zeroLoopMapHomotopy.cast
    (InputIdentityPositiveSeed.source_eq g)
    (InputIdentityPositiveSeed.target_eq g)

/-- The transition comparison retains the complete original relative conjugation track. -/
lemma positiveTransitionHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    Path.toContinuousMap
      ((positiveTransitionHomotopy g).level n (r, x)) s =
        (InputIdentityPositiveSeed.conjugateComparison g).level n (r, (s, x)) := rfl


namespace InputIdentityPositiveSeed

/-- Every coordinate of the actual old unit loop has its original full-cone image. -/
theorem oldUnit_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (oldUnit g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputSeed.oldUnit g) := by
  intro s
  rfl

/-- Every coordinate of the actual new unit loop has its original full-cone image. -/
theorem newUnit_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (newUnit g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputSeed.newUnit g) := by
  intro s
  rfl

/-- The original supplied unit intertwining retains all its comparison and path times. -/
theorem unitPasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (unitPasting g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputSeed.unitPasting g) := by
  unfold unitPasting InputSeed.unitPasting
  apply Homotopy.RelHomotopy.MappedAt.transport
  all_goals try simp only [Homotopy.postcomp_trans, oldUnit, newUnit,
    InputIdentityPositiveNull.laurentMovement, InputSeed.oldUnit,
    InputSeed.newUnit, InputNull.laurentMovement]
  intro r s
  rfl

/-- The unchanged old null after gamma retains the complete original mapped-null route. -/
theorem originalOldNull_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositiveNull.originalOldNull g).MappedAt
      (InputIdentityPositive.inclusion X) n x
      (InputNull.originalOldNull g) := by
  intro s
  rw [InputIdentityPositiveNull.originalOldNull_level,
    InputNull.originalOldNull_level]
  exact ((InputIdentityPositiveNull.oldPositive_mapped g n x).trans
    ((InputIdentityPositiveNull.positiveMovement_mapped g n x).trans
      (InputIdentityPositiveNull.oldCone_mapped g n x))) s

/-- The unchanged new null retains the complete original precomposed-null route. -/
theorem originalNewNull_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositiveNull.originalNewNull g).MappedAt
      (InputIdentityPositive.inclusion X) n x
      (InputNull.originalNewNull g) := by
  intro s
  rw [InputIdentityPositiveNull.originalNewNull_level,
    InputNull.originalNewNull_level]
  exact ((InputIdentityPositiveNull.newPositive_mapped g n x).trans
    (InputIdentityPositiveNull.newCone_mapped g n x)) s

/-- The entire chosen relative conjugation is the image of the identical positive-cone recipe. -/
theorem conjugateComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (conjugateComparison g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputSeed.conjugateComparison g) := by
  apply Homotopy.RelHomotopy.conjugateNaturality_mapped
  · exact InputIdentityPositiveNull.laurentMovement_mapped g n x
  · exact oldUnit_mapped g n x
  · exact newUnit_mapped g n x
  · exact originalNewNull_mapped g n x
  · exact unitPasting_mapped g n x
  · exact InputIdentityPositiveNull.originalNullComparison_mapped g n x

end InputIdentityPositiveSeed

/-- The whole existing chosen J0 is recovered at every original degree, comparison time,
output-loop time and source point, using the identical original unit/null recipe. -/
theorem positiveTransitionHomotopy_factor
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap
        ((positiveTransitionHomotopy g).level n (r, x)) s) =
    Path.toContinuousMap
      ((transitionInputHomotopy g).level n (r, x)) s :=
  InputIdentityPositiveSeed.conjugateComparison_mapped g n x r s

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
