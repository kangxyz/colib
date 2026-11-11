/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationUnitRoutes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative

/-! Original identity and perfect relative tracks retain all independent coordinates. -/
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
local notation "ε" => boundedAboveFlatAffineEvaluationPrespectrumMap
local notation "unitTrack" => boundedAboveFlatAffinePullbackIdHomotopy

example
    (R : CommRingCat.{u}) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationUnitHomotopy R).level n)
      ((boundedAboveFlatAffineEvaluationUnitModelHomotopy R).level n) :=
  boundedAboveFlatAffineEvaluationUnitHomotopy_level_heq R n

example (R : CommRingCat.{u}) (n : ℕ) :
    (boundedAboveFlatAffinePullbackSpecIdHomotopy R).level n = (unitTrack R).level n :=
  boundedAboveFlatAffinePullbackSpecIdHomotopy_level R n

example
    (R : CommRingCat.{u}) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level (0 + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap 0 x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).structureMap 0
        ((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level 0 (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_comm R 0 r s t x

end

end AlgebraicGeometry.Scheme.Modules
