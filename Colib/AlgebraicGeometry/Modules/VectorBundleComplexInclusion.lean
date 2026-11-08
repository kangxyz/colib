/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeWaldhausen

/-!
# The exact degree-zero inclusion of native vector bundles

The original vector bundle is placed in degree zero with its actual maps. Exactness concerns
all ambient short exact sequences of vector bundles, not only globally split sequences.
This supplies the original Waldhausen comparison map without asserting Gillet--Waldhausen.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/VectorBundleInclusion.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable (X : Scheme.{u})

instance vectorBundleComplexInclusion_additive : (vectorBundleComplexInclusion X).Additive := by
  dsimp [vectorBundleComplexInclusion]
  infer_instance

/-- The degree-zero inclusion preserves all inherited short exact sequences. -/
def vectorBundleComplexExactInclusion :
    ExactFunctor (Scheme.Modules.vectorBundleExactStructure X)
      (boundedFiniteLocallyFreeExactStructure X) where
  toFunctor := vectorBundleComplexInclusion X
  map_conflation S hS := by
    change ((S.map (ObjectProperty.ι
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M))).map
        (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)).ShortExact
    exact hS.map_of_exact _

/-- Vector-bundle isomorphisms give quasi-isomorphisms, with the actual cofibration pushouts. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/VectorBundleInclusion.lean:36-57"
    "adaptation" "Exact degree-zero inclusion with native vector bundles and actual chain maps"]
theorem vectorBundleComplexInclusion_isExact :
    Waldhausen.IsExact
      (Waldhausen.ofExactCategory (Scheme.Modules.vectorBundleExactStructure X)).cof
      (Waldhausen.ofExactCategory (Scheme.Modules.vectorBundleExactStructure X)).weq
      (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq (vectorBundleComplexInclusion X) where
  zero h := (vectorBundleComplexInclusion X).map_isZero h
  cofibration f hf := (vectorBundleComplexExactInclusion X).map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    change QuasiIso ((vectorBundleComplexInclusion X).map f).hom
    infer_instance
  pushout hi h := (vectorBundleComplexExactInclusion X).map_isPushout hi h

end Stacks.Perfect.BoundedLocallyFreeComplexes
