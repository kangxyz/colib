/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentParameterCoordinate
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.MappingCone

/-!
# The geometric Bass step and forward Laurent seed on an arbitrary scheme

The step is the actual parameter-looped cone of the geometric Bass comparison. The forward
Laurent unit is conjugated by the positive chart track followed by the specified cone
nullhomotopy. This is an objectwise construction, not a strict diagram or a raw Bass tower.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass

/-- The actual parameter-looped cone of the geometric Bass comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassStep.lean:31-33"
  "adaptation" "The original objectwise parameter-looped cone"]
def step (X : Scheme.{u}) : LoopPrespectrum.{u+1} :=
  parameterLooping (mappingCone (comparison X))

/-- The positive polynomial leg into the reduced double cylinder. -/
def sourceLeg (X : Scheme.{u}) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⟶ span X :=
  boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫ HomotopyPushout.inl _ _

/-- The positive source leg retains the actual positive chart composite. -/
theorem sourceLeg_comparison (X : Scheme.{u}) :
    sourceLeg X ≫ comparison X =
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X) := by
  let P := boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)
  let L : originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace) ⟶ span X := HomotopyPushout.inl P P
  have hL : L ≫ comparison X = boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X) :=
    comparison_inl X
  exact (Category.assoc P L (comparison X)).trans (congrArg (fun k => P ≫ k) hL)

/-- The cone nullhomotopy restricted to the positive polynomial leg. -/
def sourceLegNull (X : Scheme.{u}) :
    Homotopy ((boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
      mappingConeInclusion (comparison X))
      (zeroHom (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
        (mappingCone (comparison X))) :=
  (Homotopy.precomp (sourceLeg X) (mappingConeHomotopy (comparison X))).cast
    (by rw [← Category.assoc, sourceLeg_comparison]) rfl

/-- At every point, the restricted null track evaluates on the actual positive cone leg. -/
theorem sourceLegNull_apply (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    (sourceLegNull X).level n (s, x) =
      (mappingConeHomotopy (comparison X)).level n (s, (sourceLeg X).map n x) := rfl

/-- The prescribed source nullhomotopy first follows the positive chart and then the cone leg. -/
def sourceNull (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X) ≫
      mappingConeInclusion (comparison X))
      (zeroHom (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
        (mappingCone (comparison X))) :=
  ((plusHomotopy X).postcomp (mappingConeInclusion (comparison X))).trans (sourceLegNull X)

/-- The original forward Laurent coordinate acts along the unchanged geometric projection. -/
def unitHomotopy (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X)) :=
  boundedAboveFlatPerfectUnitHomotopy (laurentProjection.app X) (laurentScalar (op X))

/-- The original forward Laurent seed with its specified positive source nullhomotopy. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassStep.lean:49-78"
  "adaptation" "The actual forward Laurent unit and chosen positive null legs on every scheme"]
def transition (X : Scheme.{u}) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⟶ step X :=
  ((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).nullLoopMap (sourceNull X)

/-- Every loop time retains the original forward unit and both chosen null legs. -/
theorem transition_apply (X : Scheme.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((transition X).map n x) s =
      (((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).conjugateToZero
        (sourceNull X)).level n (s, x) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
