/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.VectorBundleComplexInclusion
public import Colib.KTheory.Waldhausen.CanonicalMap

/-!
# Canonical K-maps for bounded vector-bundle complexes

These are the connective S-construction K-groups and canonical maps for the actual native
Waldhausen structures. The maps retain degree-zero vector bundles, actual chain inclusions
and chosen-zero normalization. Neither map is asserted to be an equivalence.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean`,
`VectorBundleInclusion.lean`, and `KTheory.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- Connective S-construction K-groups of actual bounded finite locally free complexes. -/
abbrev boundedFiniteLocallyFreeK (X : Scheme.{u}) (n : ℕ) :=
  (boundedFiniteLocallyFreeWaldhausen X).K n

/-- The actual degree-zero vector-bundle inclusion induces the canonical normalized K-map. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/VectorBundleInclusion.lean:59-66"
    "adaptation" "The connective S-construction map of the original degree-zero inclusion"]
def vectorBundleToBoundedFiniteLocallyFreeKMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.ofExactCategory (Modules.vectorBundleExactStructure X)).K n →*
      X.boundedFiniteLocallyFreeK n :=
  Waldhausen.KMap (vectorBundleComplexInclusion_isExact X) n

/-- The actual full-chain inclusion into native perfect complexes induces its canonical K-map. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/KTheory.lean:61-65"
    "adaptation" "The original chain inclusion with native Stacks perfectness as its target"]
def boundedFiniteLocallyFreeToPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    X.boundedFiniteLocallyFreeK n →*
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n :=
  Waldhausen.KMap (boundedFiniteLocallyFreePerfectInclusion_isExact X) n

end AlgebraicGeometry.Scheme
