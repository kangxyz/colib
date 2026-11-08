/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedFiberComparison

/-! Full-signature regression consumers for the original supported fiber assembly. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

section Generic

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)

example : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
    (originalPrespectrumMap W V hF h0) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy W V hF h0

end Generic

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example : perfectSupportedPrespectrum j ≅
    originalPrespectrum (Fibration.acyclicStructure (perfectOpenNested j)) :=
  perfectSupportedAcyclicPrespectrumIso j

example : perfectSupportedToAcyclicPrespectrumMap j ≫
    Fibration.acyclicInclusionPrespectrumMap (perfectOpenNested j) =
      perfectSupportedInclusionPrespectrumMap j :=
  perfectSupportedToAcyclicPrespectrumMap_inclusion j

example : perfectSupportedFiberPrespectrumMap j ≫
    homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
      perfectSupportedInclusionPrespectrumMap j :=
  perfectSupportedFiberPrespectrumMap_projection j

example : perfectSupportedFiberPrespectrumMap j =
    homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
      (perfectSupportedInclusionPrespectrumMap j)
      (perfectSupportedPrespectrumNullhomotopy j) :=
  perfectSupportedFiberPrespectrumMap_eq_lift j

example (n : ℕ) (x : (perfectSupportedPrespectrum j).space n) (s : unitInterval) :
    ((perfectSupportedFiberPrespectrumMap j).map n x).1.2 s =
      (Fibration.acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n
        (s, (perfectSupportedToAcyclicPrespectrumMap j).map n x) := rfl

example (n : ℕ) (s t : unitInterval) (x : (perfectSupportedPrespectrum j).space n) :
    (perfectSupportedPrespectrumNullhomotopy j).level (n + 1)
        (s, (perfectSupportedPrespectrum j).structureMap n x t) =
      (perfectOpenPrespectrum j).structureMap n
        ((perfectSupportedPrespectrumNullhomotopy j).level n (s, x)) t :=
  perfectSupportedPrespectrumNullhomotopy_structure j n s t x

example (n : ℕ) (x : (perfectSupportedPrespectrum j).space n) :
    basedLoopMap ((perfectSupportedFiberPrespectrumMap j).map (n + 1))
      ((perfectSupportedFiberPrespectrumMap j).map_point (n + 1))
      ((perfectSupportedPrespectrum j).structureMap n x) =
    (homotopyFiber (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))).structureMap n
      ((perfectSupportedFiberPrespectrumMap j).map n x) :=
  (perfectSupportedFiberPrespectrumMap j).comm n x

example : IsStableEquivalence (perfectSupportedFiberPrespectrumMap j) :=
  perfectSupportedFiberPrespectrumMap_isStableEquivalence j

example : IsStableEquivalence (perfectSupportedFiberPrespectrumRebasedMap j) :=
  perfectSupportedFiberPrespectrumRebasedMap_isStableEquivalence j

example : LoopPrespectrum.Homotopy (perfectSupportedFiberPrespectrumRebasedMap j)
    (perfectSupportedFiberPrespectrumMap j) := perfectSupportedFiberPrespectrumRebaseHomotopy j

example : LoopPrespectrum.Homotopy
    (perfectSupportedFiberPrespectrumRebasedMap j ≫
      homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)))
    (exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectSupportedInclusion_isExact j)) :=
  perfectSupportedFiberPrespectrumRebasedMapProjectionHomotopy j

example (n : ℕ) : HomotopyGroup.piMap n (perfectSupportedFiberMap j)
    (perfectSupportedFiberMap_basepoint j) = perfectSupportedFiberKMap j n :=
  perfectSupportedFiberMap_piMap j n

example :
    (Fibration.originalFiberToSpectrumLevelOne (perfectOpenNested j)).toHomotopyEquiv.toFun.comp
        (perfectSupportedFiberMap j) =
      ((perfectSupportedFiberPrespectrumMap j).map 1).comp
        (perfectSupportedWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  perfectSupportedFiberPrespectrumMap_level_one_square j

example (n : ℕ) (a : PerfectSupportedK j n) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
        (Additive.ofMul (perfectSupportedKMap j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedInclusionPrespectrumMap j)
        (originalKStableEquiv (perfectSupportedWaldhausen j) n (Additive.ofMul a)) :=
  perfectSupportedInclusionPrespectrumMap_naturality j n a
