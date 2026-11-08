/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectApproximation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfect
public import Colib.KTheory.Waldhausen.Approximation.GeneralKEquivalence

/-!
# The Literal Bounded Above Flat Perfect K-Comparison

The proved relative factorization and actual identity-cone cylinders give bijectivity of the
canonical K-map of the unchanged inclusion in every nonnegative degree, including zero. The
resulting group equivalence has this same canonical inclusion K-map as its forward map.
Only quasi-compactness of the underlying space is needed.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, generalized to native ringed spaces.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry StrictlyPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

/-- The original inclusion K-map is bijective in every connective degree, including zero. -/
@[colib_tag "COL-0325",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean:33-39"
    "adaptation" "The literal canonical inclusion map, every natural degree and CompactSpace only"]
theorem boundedAboveFlatPerfectToPerfectKMap_bijective
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier] (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectToPerfectKMap X n) := by
  let : (Waldhausen.complexes (OXMod.{u, u, u} X)).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso (OXMod.{u, u, u} X)
      (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (perfectComplexesWaldhausen X).weq.HasTwoOutOfThreeProperty :=
    Waldhausen.CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact (boundedAboveFlatPerfectInclusion_approximation X).KMap_bijective_general
    (boundedAboveFlatPerfectInclusion_isExact X)
    (boundedAboveFlatPerfectJointData X (Waldhausen.Fibration.NestedWeakEquivalences.refl _)) n

/-- The bounded-above flat model computes actual perfect K-groups by the original inclusion. -/
@[colib_tag "COL-0325",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean:41-46"
    "adaptation" "The equivalence whose forward map is the canonical literal inclusion K-map"]
def boundedAboveFlatPerfectKEquiv
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier] (n : ℕ) :
    X.boundedAboveFlatPerfectK n ≃* (perfectComplexesWaldhausen X).K n :=
  MulEquiv.ofBijective (boundedAboveFlatPerfectToPerfectKMap X n)
    (boundedAboveFlatPerfectToPerfectKMap_bijective X n)

/-- The forward monoid homomorphism is definitionally the unchanged inclusion K-map. -/
@[simp]
theorem boundedAboveFlatPerfectKEquiv_coe
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier] (n : ℕ) :
    (↑(boundedAboveFlatPerfectKEquiv X n) :
      X.boundedAboveFlatPerfectK n →* (perfectComplexesWaldhausen X).K n) =
        boundedAboveFlatPerfectToPerfectKMap X n := rfl

end AlgebraicGeometry.RingedSpace
