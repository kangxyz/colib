/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedUnionPrespectrum

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

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original continuous supported fiber map, retaining the canonical acyclic path. -/
def perfectSupportedUnionFiberMap : C((perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).Delooping,
    HomotopyFiber (Fibration.changeWeakMap (perfectSupportedOpenNested j T))
      (perfectSupportedOpenWeakWaldhausen j T).kBasepoint) :=
  (Fibration.canonicalFiberMap (perfectSupportedOpenNested j T)).comp
    (deloopingMap (perfectSupportedUnionToAcyclic_exact j T)).hom

/-- The original supported fiber map preserves the actual constant-path zero. -/
theorem perfectSupportedUnionFiberMap_basepoint :
    perfectSupportedUnionFiberMap j T (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).kBasepoint =
      HomotopyFiber.basepoint (Fibration.changeWeakMap (perfectSupportedOpenNested j T))
        (perfectSupportedOpenWeakWaldhausen j T).kBasepoint
        (perfectSupportedWaldhausen T.ι).kBasepoint
        (Fibration.changeWeakMap_basepoint (perfectSupportedOpenNested j T)) := by
  change Fibration.canonicalFiberMap (perfectSupportedOpenNested j T)
    ((deloopingMap (perfectSupportedUnionToAcyclic_exact j T)).hom
      (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).kBasepoint) = _
  rw [deloopingMap_basepoint_of_zeroEq (perfectSupportedUnionToAcyclic_exact j T) rfl]
  exact Fibration.canonicalFiberMap_basepoint (perfectSupportedOpenNested j T)

/-- The actual original based map induces precisely the existing supported fiber K-map. -/
theorem perfectSupportedUnionFiberMap_piMap (n : ℕ) :
    HomotopyGroup.piMap n (perfectSupportedUnionFiberMap j T)
      (perfectSupportedUnionFiberMap_basepoint j T) = perfectSupportedUnionFiberKMap j T n := by
  change HomotopyGroup.piMap n (perfectSupportedUnionFiberMap j T) _ =
    (Fibration.canonicalFiberKMap (perfectSupportedOpenNested j T) n).comp
      (KMap (perfectSupportedUnionToAcyclic_exact j T) n)
  rw [KMap_eq_piMap_of_zeroEq (perfectSupportedUnionToAcyclic_exact j T) rfl n]
  exact HomotopyGroup.mapHom_comp (N := Fin (n + 1))
    (deloopingMap (perfectSupportedUnionToAcyclic_exact j T)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectSupportedUnionToAcyclic_exact j T) rfl)
    (Fibration.canonicalFiberMap (perfectSupportedOpenNested j T))
    (Fibration.canonicalFiberMap_basepoint (perfectSupportedOpenNested j T))

/-- Level one is the entire original supported fiber map, including its unchanged path. -/
theorem perfectSupportedUnionFiberPrespectrumMap_level_one_square :
    (Fibration.originalFiberToSpectrumLevelOne (perfectSupportedOpenNested j
      T)).toHomotopyEquiv.toFun.comp
        (perfectSupportedUnionFiberMap j T) =
      ((perfectSupportedUnionFiberPrespectrumMap j T).map 1).comp
        (perfectSupportedWaldhausen (T ⊔
          j.opensRange).ι).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  have h := ContinuousMap.congr_fun
    (Fibration.canonicalFiberPrespectrumMap_level_one_square (perfectSupportedOpenNested j T))
    ((deloopingMap (perfectSupportedUnionToAcyclic_exact j T)).hom x)
  have hx := ContinuousMap.congr_fun
    (asSmallDeloopingHomeomorph_naturality (perfectSupportedUnionToAcyclic_exact j T)) x
  exact h.trans (congrArg
    ((Fibration.canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T)).map 1) hx)

/-- Canonical zero-rebased transport into the same original relative-open fiber. -/
def perfectSupportedUnionFiberPrespectrumRebasedMap : perfectSupportedUnionPrespectrum j T ⟶
    homotopyFiber (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) :=
  exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
      (perfectSupportedUnionToAcyclic_exact j T) ≫
      Fibration.canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T)

/-- The canonical rebasing comparison is an actual coherent homotopy into the fiber itself. -/
def perfectSupportedUnionFiberPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy (perfectSupportedUnionFiberPrespectrumRebasedMap j T)
      (perfectSupportedUnionFiberPrespectrumMap j T) :=
  (perfectSupportedUnionToAcyclicPrespectrumRebaseHomotopy j T).postcomp
    (Fibration.canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T))

/-- Canonical zero-rebased transport is therefore a stable equivalence as well. -/
theorem perfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence :
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumRebasedMap j T) := by
  intro d
  rw [(perfectSupportedUnionFiberPrespectrumRebaseHomotopy j T).stableHomotopyMap_eq d]
  exact perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence j T d

/-- Its projected map agrees with the canonically rebased supported inclusion coherently. -/
def perfectSupportedUnionFiberPrespectrumRebasedMapProjectionHomotopy :
    LoopPrespectrum.Homotopy
      (perfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested
          j T)))
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
        (perfectSupportedWaldhausen T.ι)
        ((perfectSupportedUnionToAcyclic_exact j T).comp
          (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T)))) := by
  have H := (perfectSupportedUnionFiberPrespectrumRebaseHomotopy j T).postcomp
    (homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)))
  rw [perfectSupportedUnionFiberPrespectrumMap_projection] at H
  exact H.trans (perfectSupportedUnionInclusionPrespectrumRebaseHomotopy j T).symm

attribute [colib_tag "COL-0335",
  colib_ref "quillen"
    "Quillen/Waldhausen/Fibration/Prespectrum.lean"
    "comparison" "Supported specialization: the original fiber K-map is induced by the spectrum
      map"]
  perfectSupportedUnionFiberMap_piMap
  perfectSupportedUnionFiberPrespectrumMap_level_one_square

attribute [colib_tag "COL-0335"]
  perfectSupportedUnionFiberPrespectrumRebaseHomotopy
  perfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence
  perfectSupportedUnionFiberPrespectrumRebasedMapProjectionHomotopy

end AlgebraicGeometry.Scheme.Modules
