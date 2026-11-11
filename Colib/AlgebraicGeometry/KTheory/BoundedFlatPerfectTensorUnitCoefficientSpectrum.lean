/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientStageRealization
public import Colib.Topology.Prespectrum.Looping

/-!
# The genuine coefficient cell as a whole stabilized spectrum track

Curry the independently realized finite coefficient cells and assemble them into a coherent
prespectrum homotopy. Degree zero uses the original loop extension, with its original input-loop
time explicit. The positive degrees use the actual first coefficient row and unit edge. Equality
with the tensor track followed by the actual loop-tail stabilization is proved for the whole
homotopy. Ordinary loop-tail stabilization is retained literally; it is not parameter looping.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Curry the actual coefficient S-row while retaining the forward unit edge as homotopy time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:33"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def tensorUnitPullbackCoefficientStageLoop (k : ℕ) :
    C(unitInterval × stageSpace k (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)),
      Path (stagePoint (k + 1) (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
        (stagePoint (k + 1) (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))) where
  toFun z := {
    toFun s := tensorUnitPullbackCoefficientStageRealization f r k (s, z)
    continuous_toFun := by fun_prop
    source' := by
      rw [tensorUnitPullbackCoefficientStageRealization_structure]
      exact Path.source _
    target' := by
      rw [tensorUnitPullbackCoefficientStageRealization_structure]
      exact Path.target _ }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (tensorUnitPullbackCoefficientStageRealization f r k).continuous.comp continuous_swap

/-- Every positive-level continuous map is the unchanged structure image of the tensor track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:51"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientStageLoop_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageLoop f r k =
      ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).level (k + 1)
        := by
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext s
  exact tensorUnitPullbackCoefficientStageRealization_structure f r k s z.1 z.2

/-- Actual coefficient cells in positive degree, with the original loop extension in degree zero.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:64"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def tensorUnitPullbackCoefficientCellLevel (n : ℕ) :
    C(unitInterval × (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n,
      (looping (tail (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).space n) :=
  Nat.casesOn n ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level 0)
    (tensorUnitPullbackCoefficientStageLoop f r)

/-- The degree-zero extension retains the input-loop time separately from the unit-edge time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:71"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientCellLevel_zero (t s : unitInterval)
    (x : Path (stagePoint 0 (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))
      (stagePoint 0 (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))) :
    Path.toContinuousMap (tensorUnitPullbackCoefficientCellLevel f r 0 (t, x)) s =
      (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 1 (t, x s) := rfl

/-- Equality of complete continuous levels, without taking homotopy or stable classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:78"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientCellLevel_eq (n : ℕ) :
    tensorUnitPullbackCoefficientCellLevel f r n =
      ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).level n := by
  cases n with
  | zero => rfl
  | succ k => exact tensorUnitPullbackCoefficientStageLoop_eq f r k

/-- The independently realized coefficient cells form a whole structure-compatible homotopy. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:87"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def tensorUnitPullbackCoefficientSpectrumHomotopy :
    Homotopy
      (boundedAboveFlatPerfectTensorUnitPrespectrumMap f ≫
        stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (boundedAboveFlatPerfectTensorUnitPrespectrumMap f ≫
        stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) where
  level := tensorUnitPullbackCoefficientCellLevel f r
  at_zero n x := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).at_zero n x
  at_one n x := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).at_one n x
  at_point n t := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).at_point n t
  comm n t x s := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq, tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))).comm n t x s

/-- The complete realized coefficient-cell homotopy is the actual stabilized tensor homotopy. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSpectrum.lean:112"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientSpectrumHomotopy_eq :
    tensorUnitPullbackCoefficientSpectrumHomotopy f r =
      (boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  exact tensorUnitPullbackCoefficientCellLevel_eq f r n

end AlgebraicGeometry.Scheme.Modules
