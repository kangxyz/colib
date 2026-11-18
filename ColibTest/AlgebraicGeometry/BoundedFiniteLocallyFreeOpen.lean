/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreeOpen

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration Topology

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

-- Neither compactness nor quasi-separatedness is needed.
example :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedFiniteLocallyFreeOpenNested j)) :=
  boundedFiniteLocallyFreeOpen_canonicalFiberMap_isWeakHomotopyEquivalence j

example (n : ℕ) :
    (boundedFiniteLocallyFreeOpenKRestrict j n).comp
      (KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j)) n) =
        boundedFiniteLocallyFreeKRestrict j n :=
  boundedFiniteLocallyFreeOpenKRestrict_comp_changeWeak j n

example :
    (boundedFiniteLocallyFreeOpenKRestrict j 0).range =
      (boundedFiniteLocallyFreeKRestrict j 0).range :=
  range_boundedFiniteLocallyFreeOpenKRestrict_zero j

example : Function.Surjective (boundedFiniteLocallyFreeOpenKZeroToImage j) :=
  boundedFiniteLocallyFreeOpenKZeroToImage_surjective j
