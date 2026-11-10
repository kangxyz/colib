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

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level (n + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec S).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffinePerfectFlatCoefficientHomotopy f).level n (s, x)) t :=
  boundedAboveFlatAffinePerfectFlatCoefficientHomotopy_comm f n s t x

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffinePerfectEvaluationKEquiv S n
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) n a) =
      KMap (perfectFlatPullback_waldhausenExact (Spec.map f)) n
        (boundedAboveFlatAffinePerfectEvaluationKEquiv R n a) :=
  boundedAboveFlatAffinePerfectEvaluationKEquiv_naturality f n a

end

end AlgebraicGeometry.Scheme.Modules
