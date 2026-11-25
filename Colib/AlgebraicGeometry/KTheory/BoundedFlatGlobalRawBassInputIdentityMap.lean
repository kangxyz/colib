/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityComparison
public import Colib.Topology.Prespectrum.ConeSquareMapMovingCoherence
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Identity homotopies of the original global raw cone and Bass step maps

The constructed original comparison square supplies the whole cone identity directly. Parameter
looping preserves every cone-homotopy value at its independent loop time. The Laurent inclusion,
cone cylinder, original source-null, and seed are not redefined. Compatibility with the separately
chosen input source-null and seed naturality homotopies is not asserted here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable (X : Scheme.{u})

/-- The original comparison-square cone null track is filled using the produced whole Qid. -/
def comparisonConeNullSquare :=
  coneSquareIdentityMovingNullSquare (comparison X) (inputComparisonHomotopy (𝟙 X))
    (spanHomotopy X) (laurentHomotopy X) (comparisonSquare X)

/-- The actual original input cone map at the identity is homotopic to its literal identity map. -/
def coneHomotopy : Homotopy (coneMap (𝟙 X)) (𝟙 (mappingCone (comparison X))) :=
  coneSquareIdentityHomotopyOfSquare (comparison X) (inputComparisonHomotopy (𝟙 X))
    (spanHomotopy X) (laurentHomotopy X) (comparisonSquare X)

/-- Every Laurent inclusion value follows the unchanged original Laurent identity track. -/
theorem coneHomotopy_inclusion (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (W (laurent.obj X))).space n) :
    (coneHomotopy X).level n (r, (mappingConeInclusion (comparison X)).map n x) =
      (mappingConeInclusion (comparison X)).map n ((laurentHomotopy X).level n (r, x)) := rfl

/-- The entire original cone cylinder keeps the actual constructed two-parameter null square. -/
theorem coneHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : (span X).space n) :
    (coneHomotopy X).level n
      (r, ReducedMappingCone.cylinder ((span X).point n)
        ((originalPrespectrum (W (laurent.obj X))).point n)
        ((comparison X).map n) (s, x)) =
      (comparisonConeNullSquare X).level n (r, (s, x)) := rfl

/-- Parameter-correct looping gives the whole identity of the unchanged original raw Bass map. -/
def mapHomotopy : Homotopy (map (𝟙 X)) (𝟙 (step X)) :=
  (coneHomotopy X).parameterLooping.cast rfl
    (parameterLoopingFunctor.map_id (mappingCone (comparison X)))

/-- Homotopy time and the original loop coordinate remain independent at every native level. -/
theorem mapHomotopy_apply (n : ℕ) (r s : unitInterval) (γ : (step X).space n) :
    Path.toContinuousMap ((mapHomotopy X).level n (r, γ)) s =
      (coneHomotopy X).level n (r, Path.toContinuousMap γ s) := rfl

/-- On the original seed the whole original unit loop and both original source-null legs remain. -/
theorem mapHomotopy_transition_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W X)).space n) :
    Path.toContinuousMap ((mapHomotopy X).level n (r, (transition X).map n x)) s =
      (coneHomotopy X).level n
        (r, (((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).conjugateToZero
          (sourceNull X)).level n (s, x)) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
