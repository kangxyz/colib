/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative

/-! Actual perfect endpoints and their exact flatness boundary. -/
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

example (R : CommRingCat.{u}) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedAboveFlatAffinePerfectEvaluationMap R)) :=
  boundedAboveFlatAffinePerfectEvaluationMap_isStableEquivalence R d

example (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffinePerfectEvaluationKEquiv R n a =
      boundedAboveFlatPerfectToPerfectKMap (Spec R).toRingedSpace n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) :=
  boundedAboveFlatAffinePerfectEvaluationKEquiv_apply R n a

example
    (R : CommRingCat.{u}) (n : ℕ) (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
        (boundedAboveFlatAffinePerfectEvaluationKEquiv R n a) =
      HomotopyGroup.map ((boundedAboveFlatAffinePerfectEvaluationMap R).map 0)
        ((boundedAboveFlatAffinePerfectEvaluationMap R).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a) :=
  boundedAboveFlatAffinePerfectEvaluationKEquiv_zeroSpace R n a

end

end AlgebraicGeometry.Scheme.Modules
