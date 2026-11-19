/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreeGilletWaldhausen

@[expose] public noncomputable section

open AlgebraicGeometry
universe u

-- The actual degree-zero Waldhausen map is bijective also on K₀.
example (X : Scheme.{u}) : Function.Bijective (X.vectorBundleToBoundedFiniteLocallyFreeKMap 0) :=
  X.vectorBundleToBoundedFiniteLocallyFreeKMap_bijective 0

-- The forward map of the all-degree public Quillen comparison is the original composite.
example (X : Scheme.{u}) (n : ℕ) :
    (↑(X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv n) : X.K n →*
      X.boundedFiniteLocallyFreeK n) =
      X.vectorBundleKToBoundedFiniteLocallyFreeKMap n :=
  X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv_toMonoidHom n

-- This is an equivalence with bounded vector-bundle complexes, not all perfect complexes.
example (X : Scheme.{u}) (n : ℕ) : X.K n ≃* X.boundedFiniteLocallyFreeK n :=
  X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv n

-- The public comparison with all perfect complexes agrees with the original composite.
example (X : Scheme.{u}) (n : ℕ) :
    (X.boundedFiniteLocallyFreeToPerfectKMap n).comp
      (X.vectorBundleKToBoundedFiniteLocallyFreeKMap n) = X.vectorBundleKToPerfectKMap n :=
  X.boundedFiniteLocallyFreeToPerfectKMap_comp_vectorBundleKToBoundedFiniteLocallyFreeKMap n

-- Keep the K₀ composite tied to the exact forward map of the equivalence.
example (X : Scheme.{u}) :
    (X.boundedFiniteLocallyFreeToPerfectKMap 0).comp
      (↑(X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv 0)) =
        X.vectorBundleKToPerfectKMap 0 := by
  rw [X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv_toMonoidHom 0]
  exact X.boundedFiniteLocallyFreeToPerfectKMap_comp_vectorBundleKToBoundedFiniteLocallyFreeKMap 0
