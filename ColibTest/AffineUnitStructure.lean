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
    (R : CommRingCat.{u}) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (1, x)) = (ε R).map n x :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_target R n r x

example
    (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).point n :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_point R n r s

example
    (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationUnitRelHomotopy R).level n (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationUnitRelHomotopy_comm R n r s t x

end

end AlgebraicGeometry.Scheme.Modules
