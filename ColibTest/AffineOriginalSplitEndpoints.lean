/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative

/-! Strong symbolic consumers of all actual relative-composition boundary coordinates. -/
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
local notation "P" => boundedAboveFlatAffinePullbackModelMap
local notation "a" => boundedAboveFlatAffineSectionPrespectrumFunctor.map
local notation "ε" => boundedAboveFlatAffineEvaluationPrespectrumMap

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).level n (s, x) :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_at_zero f g n s x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (1, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy f g).level n (s, x) :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_at_one f g n s x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (0, x)) =
      (ε T).map n ((a (f ≫ g)).map n x) :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_source f g n r x

end AlgebraicGeometry.Scheme.Modules
