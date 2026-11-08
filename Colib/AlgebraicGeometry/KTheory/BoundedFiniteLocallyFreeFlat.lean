/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeFlat
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfect
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFree
public import Colib.KTheory.Waldhausen.Functoriality

/-!
# The Canonical Strict-to-Flat K-Map

The actual bounded vector-bundle inclusion induces its connective K-map. Its composite with
the literal flat-to-perfect K-map is the original bounded-vector-bundle-to-perfect K-map.
The identity includes degree zero and retains the existing chosen-zero normalization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- The canonical K-map of the actual bounded-vector-bundle-to-flat chain inclusion. -/
def boundedFiniteLocallyFreeToFlatKMap (X : Scheme.{u}) (n : ℕ) :
    X.boundedFiniteLocallyFreeK n →* X.toRingedSpace.boundedAboveFlatPerfectK n :=
  Waldhausen.KMap (boundedFiniteLocallyFreeFlatInclusion_isExact X) n

/-- Literal inclusion composition gives the unchanged original perfect comparison map. -/
@[colib_tag "COL-0323",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:87-92"
    "adaptation" "The original composite of literal inclusion K-maps in every connective degree"]
theorem boundedAboveFlatPerfectToPerfectKMap_comp (X : Scheme.{u}) (n : ℕ) :
    (X.toRingedSpace.boundedAboveFlatPerfectToPerfectKMap n).comp
      (boundedFiniteLocallyFreeToFlatKMap X n) = boundedFiniteLocallyFreeToPerfectKMap X n := by
  unfold RingedSpace.boundedAboveFlatPerfectToPerfectKMap boundedFiniteLocallyFreeToFlatKMap
    boundedFiniteLocallyFreeToPerfectKMap
  rw [Waldhausen.KMap_comp_KMap]
  rfl

end AlgebraicGeometry.Scheme
