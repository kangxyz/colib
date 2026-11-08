/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedFiberComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrackTransport

/-!
# The actual connective open image-cover diagram

The target is the existing coarse prespectrum, not a second cover construction.
Its Omega property and supported fiber comparison need no geometric assumptions.
The existing whole raw restriction homotopy identifies its composite with flat restriction;
here we expose the resulting equality of actual stable maps in every integer degree.
This module does not assert positive bijectivity without geometric inputs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The existing coarse target has weak-equivalence structure maps at every level,
including the component condition. No replacement of its spaces or maps is made. -/
theorem perfectOpenPrespectrum_isOmega : IsOmega (perfectOpenPrespectrum j) :=
  originalPrespectrum_isOmega (perfectOpenWeakWaldhausen j)

/-- The actual factorization induces the ordinary flat restriction in every stable degree.
The underlying whole homotopy is `perfectOpenOriginalRestrictionFlatHomotopy`. -/
theorem perfectOpenRestrictPrespectrumMap_comp_stable (k : ℤ) :
    (stableHomotopyFunctor k).map
        (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) ≫
      (stableHomotopyFunctor k).map (perfectOpenRestrictPrespectrumMap j) =
        (stableHomotopyFunctor k).map (perfectFlatPrespectrumMap j) := by
  rw [← Functor.map_comp]
  exact (perfectOpenOriginalRestrictionFlatHomotopy j).stableHomotopyMap_eq k

end AlgebraicGeometry.Scheme.Modules
