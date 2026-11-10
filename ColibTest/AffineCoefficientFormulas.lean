/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients

/-! Actual perfect endpoints and their exact flatness boundary. -/
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffineEvaluationKEquiv S n
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) n a) =
      KMap (boundedAboveFlatPerfectPullback_isExact (Spec.map f)) n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) :=
  boundedAboveFlatAffineEvaluationKEquiv_naturality f n a

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) (a : (boundedAboveFlatAffineSectionWaldhausen R).K 0) :
    boundedAboveFlatAffineEvaluationKEquiv S 0
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) 0 a) =
      KMap (boundedAboveFlatPerfectPullback_isExact (Spec.map f)) 0
        (boundedAboveFlatAffineEvaluationKEquiv R 0 a) :=
  boundedAboveFlatAffineEvaluationKEquiv_naturality f 0 a

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level (n + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n (s, x)) t :=
  boundedAboveFlatAffineEvaluationCoefficientHomotopy_comm f n s t x

example
    {R S : CommRingCat.{u}} (f : R ⟶ S) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level (0 + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap 0 x t) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)).structureMap 0
        ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level 0 (s, x)) t :=
  boundedAboveFlatAffineEvaluationCoefficientHomotopy_comm f 0 s t x

end

end AlgebraicGeometry.Scheme.Modules
