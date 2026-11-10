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
    (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy R).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec R).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy R).level n (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationUnitPerfectRelHomotopy_comm R n r s t x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy f g).level n
          (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy_comm f g n r s t x

end

end AlgebraicGeometry.Scheme.Modules
