/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedUnionFiberNaturality

/-!
# The original union-supported fiber square

The original union-support functor and inverse flattening commute before normalization.
Composition and chosen-zero tracks transport this square to the actual canonical fiber.
-/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

example :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w)
      (exactOriginalPrespectrumMap
          (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
          (boundedAboveFlatPerfectSupportedWaldhausen (S ⊔ j'.opensRange).ι)
          (boundedAboveFlatPerfectSupportedPullback_isExact
            (supportedPairUnionSquare j' j f g w)) ≫
        boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j' S) :=
  boundedAboveFlatPerfectSupportedUnionFiberPullbackHomotopy j' j f g w

end AlgebraicGeometry.Scheme.Modules
