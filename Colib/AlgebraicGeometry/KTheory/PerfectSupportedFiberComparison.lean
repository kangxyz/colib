/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPrespectrum

/-!
# Original supported fiber coordinates and canonical rebasing

The actual supported fiber comparison recovers the old based homotopy-fiber map and
its existing canonical K-map at level one. Canonically rebased transport also gives a
stable equivalence by the explicitly constructed coherent homotopy, not an assumed
comparison. Neither construction replaces the original acyclic nullhomotopy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original continuous supported fiber map, retaining the canonical acyclic path. -/
def perfectSupportedFiberMap : C((perfectSupportedWaldhausen j).Delooping,
    HomotopyFiber (Fibration.changeWeakMap (perfectOpenNested j))
      (perfectOpenWeakWaldhausen j).kBasepoint) :=
  (Fibration.canonicalFiberMap (perfectOpenNested j)).comp
    (deloopingMap (perfectSupportedToAcyclic_exact j)).hom

/-- The original supported fiber map preserves the actual constant-path zero. -/
theorem perfectSupportedFiberMap_basepoint :
    perfectSupportedFiberMap j (perfectSupportedWaldhausen j).kBasepoint =
      HomotopyFiber.basepoint (Fibration.changeWeakMap (perfectOpenNested j))
        (perfectOpenWeakWaldhausen j).kBasepoint
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint
        (Fibration.changeWeakMap_basepoint (perfectOpenNested j)) := by
  change Fibration.canonicalFiberMap (perfectOpenNested j)
    ((deloopingMap (perfectSupportedToAcyclic_exact j)).hom
      (perfectSupportedWaldhausen j).kBasepoint) = _
  rw [deloopingMap_basepoint_of_zeroEq (perfectSupportedToAcyclic_exact j) rfl]
  exact Fibration.canonicalFiberMap_basepoint (perfectOpenNested j)

/-- The actual original based map induces precisely the existing supported fiber K-map. -/
theorem perfectSupportedFiberMap_piMap (n : ℕ) :
    HomotopyGroup.piMap n (perfectSupportedFiberMap j)
      (perfectSupportedFiberMap_basepoint j) = perfectSupportedFiberKMap j n := by
  change HomotopyGroup.piMap n (perfectSupportedFiberMap j) _ =
    (Fibration.canonicalFiberKMap (perfectOpenNested j) n).comp
      (KMap (perfectSupportedToAcyclic_exact j) n)
  rw [KMap_eq_piMap_of_zeroEq (perfectSupportedToAcyclic_exact j) rfl n]
  exact HomotopyGroup.mapHom_comp (N := Fin (n + 1))
    (deloopingMap (perfectSupportedToAcyclic_exact j)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectSupportedToAcyclic_exact j) rfl)
    (Fibration.canonicalFiberMap (perfectOpenNested j))
    (Fibration.canonicalFiberMap_basepoint (perfectOpenNested j))

/-- Level one is the entire original supported fiber map, including its unchanged path. -/
theorem perfectSupportedFiberPrespectrumMap_level_one_square :
    (Fibration.originalFiberToSpectrumLevelOne (perfectOpenNested j)).toHomotopyEquiv.toFun.comp
        (perfectSupportedFiberMap j) =
      ((perfectSupportedFiberPrespectrumMap j).map 1).comp
        (perfectSupportedWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  have h := ContinuousMap.congr_fun
    (Fibration.canonicalFiberPrespectrumMap_level_one_square (perfectOpenNested j))
    ((deloopingMap (perfectSupportedToAcyclic_exact j)).hom x)
  have hx := ContinuousMap.congr_fun
    (asSmallDeloopingHomeomorph_naturality (perfectSupportedToAcyclic_exact j)) x
  exact h.trans (congrArg
    ((Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)).map 1) hx)

/-- Canonical zero-rebased transport into the same original relative-open fiber. -/
def perfectSupportedFiberPrespectrumRebasedMap : perfectSupportedPrespectrum j ⟶
    homotopyFiber (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) :=
  exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
    (Fibration.acyclicStructure (perfectOpenNested j)) (perfectSupportedToAcyclic_exact j) ≫
      Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)

/-- The canonical rebasing comparison is an actual coherent homotopy into the fiber itself. -/
def perfectSupportedFiberPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy (perfectSupportedFiberPrespectrumRebasedMap j)
      (perfectSupportedFiberPrespectrumMap j) :=
  (perfectSupportedToAcyclicPrespectrumRebaseHomotopy j).postcomp
    (Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j))

/-- Canonical zero-rebased transport is therefore a stable equivalence as well. -/
theorem perfectSupportedFiberPrespectrumRebasedMap_isStableEquivalence :
    IsStableEquivalence (perfectSupportedFiberPrespectrumRebasedMap j) := by
  intro d
  rw [(perfectSupportedFiberPrespectrumRebaseHomotopy j).stableHomotopyMap_eq d]
  exact perfectSupportedFiberPrespectrumMap_isStableEquivalence j d

/-- Its projected map agrees with the canonically rebased supported inclusion coherently. -/
def perfectSupportedFiberPrespectrumRebasedMap_projectionHomotopy :
    LoopPrespectrum.Homotopy
      (perfectSupportedFiberPrespectrumRebasedMap j ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)))
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectSupportedInclusion_isExact j)) := by
  have H := (perfectSupportedFiberPrespectrumRebaseHomotopy j).postcomp
    (homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)))
  rw [perfectSupportedFiberPrespectrumMap_projection] at H
  exact H.trans (perfectSupportedInclusionPrespectrumRebaseHomotopy j).symm

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0319",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenLongExactSequence.lean:39-81"
    "comparison" "The original supported fiber K-map is induced by the constructed spectrum map"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberMap_piMap
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumMap_level_one_square

attribute [colib_tag "COL-0319"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumRebaseHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumRebasedMap_isStableEquivalence
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumRebasedMap_projectionHomotopy
