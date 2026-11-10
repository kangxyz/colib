/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpen
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport

/-!
# The original bounded-flat relative-open K-model

The literal inclusion compares the relative categories on the ambient scheme.
It does not identify the target with all perfect complexes on the open.

Adapted from Quillen `BoundedFlat/OpenComparison.lean:74-114` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Connective K-groups of the actual relative bounded-flat category. -/
abbrev BoundedAboveFlatPerfectOpenK (n : ℕ) :=
  (boundedAboveFlatPerfectOpenWaldhausen j).K n

/-- The original identity functor enlarges the weak class and leaves all objects unchanged. -/
def boundedAboveFlatPerfectOpenKMap (n : ℕ) :
    X.toRingedSpace.boundedAboveFlatPerfectK n →* BoundedAboveFlatPerfectOpenK j n :=
  KMap (changeWeak_exact (boundedAboveFlatPerfectOpenNested j)) n

/-- The original inclusion gives the specified relative K-map. -/
def boundedAboveFlatPerfectOpenToPerfectOpenKMap (n : ℕ) :
    BoundedAboveFlatPerfectOpenK j n →* PerfectOpenK j n :=
  KMap (boundedAboveFlatPerfectOpenInclusion_isExact j) n

/-- The original relative inclusion K-map is bijective, including degree zero. -/
@[colib_tag "COL-0386",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenComparison.lean:89-93"
    "adaptation" "Original relative inclusion K-map bijective in every connective degree"]
theorem boundedAboveFlatPerfectOpenToPerfectOpenKMap_bijective [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n) :=
  (boundedAboveFlatPerfectOpenInclusion_approximation j).KMap_bijective_general
    (boundedAboveFlatPerfectOpenInclusion_isExact j)
    ((boundedAboveFlatPerfectOpenJointData j).coarseReflexive
      (boundedAboveFlatPerfectOpenNested j)) n

/-- The relative equivalence has the original inclusion as its forward homomorphism. -/
def boundedAboveFlatPerfectOpenKEquiv [CompactSpace X] (n : ℕ) :
    BoundedAboveFlatPerfectOpenK j n ≃* PerfectOpenK j n :=
  MulEquiv.ofBijective (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n)
    (boundedAboveFlatPerfectOpenToPerfectOpenKMap_bijective j n)

@[simp]
theorem boundedAboveFlatPerfectOpenKEquiv_coe [CompactSpace X] (n : ℕ) :
    (↑(boundedAboveFlatPerfectOpenKEquiv j n) :
      BoundedAboveFlatPerfectOpenK j n →* PerfectOpenK j n) =
        boundedAboveFlatPerfectOpenToPerfectOpenKMap j n := rfl

/-- Both routes retain exactly the original inclusion and change-of-weak K-maps. -/
theorem boundedAboveFlatPerfectOpenToPerfectOpenKMap_changeWeak (n : ℕ) :
    (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n).comp
        (boundedAboveFlatPerfectOpenKMap j n) =
      (perfectOpenKMap j n).comp (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n) :=
  (KMap_comp_KMap (changeWeak_exact (boundedAboveFlatPerfectOpenNested j))
    (boundedAboveFlatPerfectOpenInclusion_isExact j) n).trans
      (KMap_comp_KMap (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace)
        (changeWeak_exact (perfectOpenNested j)) n).symm

end AlgebraicGeometry.Scheme.Modules
