/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.PointNormDictionary

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.NativeTorusPolynomial
open AlgebraicGeometry.MotivicCohomology.WeightOne

universe u
noncomputable section
variable (k : Type u) [Field k]

example (a : kˣ) : pointCycleNorm k ((Cor.graphFunctor k).map (rationalPoint k a)) =
    Additive.ofMul a := pointCycleNorm_graph k a

example (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    pointCycleNorm k (pointGenerator k Z m) = m • Additive.ofMul Z.coordinateNorm :=
  pointCycleNorm_generator k Z m

example (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    (pointCycleNorm k (pointGenerator k Z m)).toMul = Z.coordinateNorm ^ m :=
  pointCycleNorm_generator_toMul k Z m

example (Z : PrimePoint (𝟙 (Spec (.of k)))) :
    (pointCycleNorm k (pointGenerator k Z (-1))).toMul = Z.coordinateNorm ^ (-1 : ℤ) :=
  pointCycleNorm_generator_toMul k Z (-1)

example : pointCycleNorm k (torusIdentityGraph k (base (Spec (.of k)))) = 0 :=
  pointCycleNorm_identityGraph k

example (z : point k ⟶ pointTarget k) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z)) =
        ULift.up (pointCycleNorm k z) := reducedPointNorm_toReduced k z

example (a : kˣ) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k))
        (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a)))) =
      ULift.up (Additive.ofMul a) := reducedPointNorm_graph k a

example (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up (pointGenerator k Z m))) =
      ULift.up (m • Additive.ofMul Z.coordinateNorm) := reducedPointNorm_generator k Z m
