/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.KTheory.Waldhausen.CanonicalMap

/-!
# The Literal Bounded Above Flat Perfect Inclusion K-Map

These are connective S-construction K-groups of the actual exact chain model. The forward
map is the canonical chosen-zero-normalized K-map of its literal inclusion into native perfect
complexes, in every degree including zero. No bijectivity or inverse is asserted here.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

/-- Connective S-construction K-groups of the actual bounded-above flat perfect model. -/
abbrev boundedAboveFlatPerfectK (X : RingedSpace.{u, u}) (n : ℕ) :=
  (boundedAboveFlatPerfectWaldhausen X).K n

/-- The literal inclusion induces its actual canonical normalized K-map in every degree. -/
@[colib_tag "COL-0323",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:81-85"
    "adaptation" "The original forward chain inclusion, retaining every connective degree"]
def boundedAboveFlatPerfectToPerfectKMap (X : RingedSpace.{u, u}) (n : ℕ) :
    X.boundedAboveFlatPerfectK n →* (perfectComplexesWaldhausen X).K n :=
  Waldhausen.KMap (boundedAboveFlatPerfectInclusion_isExact X) n

/-- The declared forward map is definitionally the K-map of the actual inclusion. -/
@[simp]
theorem boundedAboveFlatPerfectToPerfectKMap_eq (X : RingedSpace.{u, u}) (n : ℕ) :
    boundedAboveFlatPerfectToPerfectKMap X n =
      Waldhausen.KMap (boundedAboveFlatPerfectInclusion_isExact X) n := rfl

end AlgebraicGeometry.RingedSpace
