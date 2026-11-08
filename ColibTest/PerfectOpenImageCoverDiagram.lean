/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectOpenImageCoverDiagram

/-! Full-signature consumers for the unchanged actual image-cover diagram. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example : IsOmega (perfectOpenPrespectrum j) := perfectOpenPrespectrum_isOmega j

example (k : ℤ) (hk : k < 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenPrespectrum j) k) :=
  perfectOpenPrespectrum_neg_subsingleton j k hk

example : Homotopy
    (Fibration.changeWeakPrespectrumMap (perfectOpenNested j) ≫
      perfectOpenRestrictPrespectrumMap j) (perfectFlatPrespectrumMap j) :=
  perfectOpenOriginalRestrictionFlatHomotopy j

example (k : ℤ) :
    (stableHomotopyFunctor k).map
        (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) ≫
      (stableHomotopyFunctor k).map (perfectOpenRestrictPrespectrumMap j) =
        (stableHomotopyFunctor k).map (perfectFlatPrespectrumMap j) :=
  perfectOpenRestrictPrespectrumMap_comp_stable j k

example : perfectSupportedFiberPrespectrumMap j =
    homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
      (perfectSupportedInclusionPrespectrumMap j) (perfectSupportedPrespectrumNullhomotopy j) :=
  perfectSupportedFiberPrespectrumMap_eq_lift j

example : perfectSupportedFiberPrespectrumMap j ≫
    homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
      perfectSupportedInclusionPrespectrumMap j :=
  perfectSupportedFiberPrespectrumMap_projection j

example (n : ℕ) (x : (perfectSupportedPrespectrum j).space n) (s : unitInterval) :
    ((perfectSupportedFiberPrespectrumMap j).map n x).1.2 s =
      (perfectSupportedPrespectrumNullhomotopy j).level n (s, x) :=
  perfectSupportedFiberPrespectrumMap_path j n x s

example (n : ℕ) (s t : unitInterval) (x : (perfectSupportedPrespectrum j).space n) :
    (perfectSupportedPrespectrumNullhomotopy j).level (n + 1)
        (s, (perfectSupportedPrespectrum j).structureMap n x t) =
      (perfectOpenPrespectrum j).structureMap n
        ((perfectSupportedPrespectrumNullhomotopy j).level n (s, x)) t :=
  perfectSupportedPrespectrumNullhomotopy_structure j n s t x

example (k : ℤ) :
    IsIso ((stableHomotopyFunctor k).map (perfectSupportedFiberPrespectrumMap j)) :=
  perfectSupportedFiberPrespectrumMap_isStableEquivalence j k

example (k : ℤ) :
    IsIso ((stableHomotopyFunctor k).map (perfectSupportedFiberPrespectrumRebasedMap j)) :=
  perfectSupportedFiberPrespectrumRebasedMap_isStableEquivalence j k

example : Homotopy
    (perfectSupportedFiberPrespectrumRebasedMap j ≫
      homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)))
    (exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectSupportedInclusion_isExact j)) :=
  perfectSupportedFiberPrespectrumRebasedMapProjectionHomotopy j
