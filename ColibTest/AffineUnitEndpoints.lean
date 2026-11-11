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
    (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationUnitHomotopy R).level n (s, x) :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_at_zero R n s x

example
    (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (1, (s, x)) = (ε R).map n x :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_at_one R n s x

example
    (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (0, x)) = (ε R).map n x :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_source R n r x

end

end AlgebraicGeometry.Scheme.Modules
