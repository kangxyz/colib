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
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (1, x)) =
      (prespectrumMap (P g)).map n ((prespectrumMap (P f)).map n ((ε R).map n x)) :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_target f g n r x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).point n :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_point f g n r s

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_comm f g n r s t x

end AlgebraicGeometry.Scheme.Modules
