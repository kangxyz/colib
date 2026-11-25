/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputUnit
public import Colib.Topology.Prespectrum.RelativeHomotopyConjugation
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# The actual global raw forward seed under every scheme arrow

The complete original unit and source-null comparisons give a homotopy between the two
literal raw forward-seed composites. Comparison, output-loop and structure coordinates
remain independent. This is a one-step input law, without strict functoriality or a tower.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

namespace InputSeed

/-- The original old unit loop after Laurent scheme-arrow change and target cone inclusion. -/
def oldUnit := (InputUnit.oldUnit g).postcomp
  (mappingConeInclusion (comparison X))

/-- The original new unit loop after base scheme-arrow change and target cone inclusion. -/
def newUnit := (InputUnit.newUnit g).postcomp
  (mappingConeInclusion (comparison X))

/-- The proved unit pasting retains every original coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit g).trans (InputNull.laurentMovement g)).RelHomotopy
      ((InputNull.laurentMovement g).trans (newUnit g)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit,
    InputNull.laurentMovement] using
    (laurentUnitPasting g).postcomp
      (mappingConeInclusion (comparison X))

/-- Cancel the proved actual moving Laurent track inside the two original null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (InputNull.laurentMovement g)
    (oldUnit g) (newUnit g) (InputNull.originalOldNull g)
    (InputNull.originalNewNull g)
    (unitPasting g) (InputNull.originalNullComparison g)

/-- The source based-loop map is the literal original transition followed by the actual step map. -/
lemma source_eq :
    ((oldUnit g).conjugateToZero (InputNull.originalOldNull g)).zeroLoopMap =
      transition Y ≫ map g := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit g).conjugateToZero
    (InputNull.originalOldNull g)).level n (s, x) =
    ((((unitHomotopy Y).postcomp
      (mappingConeInclusion (comparison Y))).conjugateToZero
        (sourceNull Y)).postcomp
          (coneMap g)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target based-loop map is the literal base input map followed by the new transition. -/
lemma target_eq :
    ((newUnit g).conjugateToZero (InputNull.originalNewNull g)).zeroLoopMap =
      boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        transition X := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit g).conjugateToZero
    (InputNull.originalNewNull g)).level n (s, x) =
    (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
      (((unitHomotopy X).postcomp
        (mappingConeInclusion (comparison X))).conjugateToZero
          (sourceNull X))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end InputSeed

/-- Every scheme arrow gives a genuine whole homotopy of the original Bass transitions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputSeed.lean:98-111"
  "adaptation" "The prescribed input homotopy retaining all original loop times"]
def transitionInputHomotopy :
    Homotopy (transition Y ≫ map g)
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        transition X) :=
  (InputSeed.conjugateComparison g).zeroLoopMapHomotopy.cast
    (InputSeed.source_eq g) (InputSeed.target_eq g)

/-- The transition comparison retains the complete original relative conjugation track. -/
lemma transitionInputHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    Path.toContinuousMap
      ((transitionInputHomotopy g).level n (r, x)) s =
        (InputSeed.conjugateComparison g).level n (r, (s, x)) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
