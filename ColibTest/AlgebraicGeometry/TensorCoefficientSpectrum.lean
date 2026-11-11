/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientSpectrum
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.CoefficientSpectrumTest
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

example (k : ℕ) (s t : unitInterval)
    (x : stageSpace k (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))) :
    tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).structureMap (k + 1)
        ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level (k + 1) (t, x)) s :=
  tensorUnitPullbackCoefficientStageRealization_structure f r k s t x

example (k : ℕ) :
    tensorUnitPullbackCoefficientStageRealization f r k =
      ⟨fun z => (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).structureMap (k + 1)
        ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level (k + 1) (z.2.1, z.2.2)) z.1,
        by fun_prop⟩ :=
  tensorUnitPullbackCoefficientStageRealization_eq f r k

example (t s : unitInterval)
    (x : Path (stagePoint 0 (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))
      (stagePoint 0 (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))) :
    Path.toContinuousMap (tensorUnitPullbackCoefficientCellLevel f r 0 (t, x)) s =
      (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 1 (t, x s) :=
  tensorUnitPullbackCoefficientCellLevel_zero f r t s x

example :
    tensorUnitPullbackCoefficientSpectrumHomotopy f r =
      (boundedAboveFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) :=
  tensorUnitPullbackCoefficientSpectrumHomotopy_eq f r

end AlgebraicGeometry.Scheme.Modules.CoefficientSpectrumTest
