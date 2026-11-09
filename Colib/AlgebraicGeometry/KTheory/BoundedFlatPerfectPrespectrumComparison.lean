/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectComparison
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual bounded-above flat to perfect prespectrum comparison

The canonical zero-normalized map of the literal inclusion is a stable equivalence on
compact ringed spaces. Its forward map in every connective K-degree is unchanged.
The affine case uses compactness of Spec, without a Noetherian hypothesis. Stability
here uses connectivity of the original models, not negative Bass localization, and
asserts no levelwise homotopy equivalence.

Implementation provenance: Quillen `PerfectComplexes/BoundedFlat/KComparison.lean` and
`Waldhausen/SConstruction/Iterated/StableFunctoriality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, applied to the native ringed-space inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

/-- The actual normalized map of the literal bounded-above flat perfect inclusion. -/
def boundedAboveFlatPerfectToPerfectPrespectrumMap (X : RingedSpace.{u, u}) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen X) ⟶
      originalPrespectrum (perfectComplexesWaldhausen X) :=
  exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectInclusion_isExact X)

/-- Compactness makes the actual inclusion map stable in every integer degree. -/
theorem boundedAboveFlatPerfectToPerfectPrespectrumMap_isStableEquivalence
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier] :
    IsStableEquivalence (boundedAboveFlatPerfectToPerfectPrespectrumMap X) :=
  (exactOriginalPrespectrumMap_isStableEquivalence_iff _ _
    (boundedAboveFlatPerfectInclusion_isExact X)).mpr
      (boundedAboveFlatPerfectToPerfectKMap_bijective X)

/-- The induced stable map is the unchanged forward inclusion K-map, including K0. -/
theorem boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality
    (X : RingedSpace.{u, u}) (n : ℕ) (a : X.boundedAboveFlatPerfectK n) :
    originalKStableEquiv (perfectComplexesWaldhausen X) n
        (Additive.ofMul (boundedAboveFlatPerfectToPerfectKMap X n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatPerfectToPerfectPrespectrumMap X)
        (originalKStableEquiv (boundedAboveFlatPerfectWaldhausen X) n (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality _ _ (boundedAboveFlatPerfectInclusion_isExact X) n a

/-- The zeroth-space comparison also retains the literal K-map in all connective degrees. -/
theorem boundedAboveFlatPerfectToPerfectPrespectrumMap_zeroSpace_naturality
    (X : RingedSpace.{u, u}) (n : ℕ) (a : X.boundedAboveFlatPerfectK n) :
    originalZeroSpaceEquiv (perfectComplexesWaldhausen X) n
        (boundedAboveFlatPerfectToPerfectKMap X n a) =
      HomotopyGroup.map ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map 0)
        ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map_point 0)
        (originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen X) n a) :=
  exactOriginalZeroSpaceEquiv_naturality _ _ (boundedAboveFlatPerfectInclusion_isExact X) n a

/-- On Spec of any commutative ring, the same actual inclusion is a stable equivalence. -/
theorem boundedAboveFlatPerfectSpecPrespectrumMap_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence
      (boundedAboveFlatPerfectToPerfectPrespectrumMap
        (Scheme.Spec.obj (Opposite.op R)).toRingedSpace) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_isStableEquivalence _

end AlgebraicGeometry.RingedSpace

attribute [colib_tag "COL-0351",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean"
    "adaptation" "Actual normalized inclusion stable equivalence and unchanged connective K-map"]
  AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectToPerfectPrespectrumMap
  AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectToPerfectPrespectrumMap_isStableEquivalence
  AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality
  AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectToPerfectPrespectrumMap_zeroSpace_naturality
  AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectSpecPrespectrumMap_isStableEquivalence
