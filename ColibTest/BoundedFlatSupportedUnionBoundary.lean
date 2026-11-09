/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedUnionPrespectrum

/-! Explicit zero and negative-one boundaries for the actual supported coarse fiber. -/
noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example :
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T 0).toMonoidHom =
      KMap (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j T) 0 :=
  boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_forward j T 0

example :
    (boundedAboveFlatPerfectSupportedUnionKMap j T 0).comp
        (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T 0).toMonoidHom =
      KMap (Fibration.acyclicInclusion_exact
        (boundedAboveFlatPerfectSupportedOpenNested j T)) 0 :=
  boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inclusion j T 0

example (a : BoundedAboveFlatPerfectSupportedOpenK j T 1) :
    boundedAboveFlatPerfectSupportedUnionFiberKMap j T 0
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T 0 a) =
      HomotopyFiber.connectingHom
        (Fibration.changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
        (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint
        (boundedAboveFlatPerfectSupportedWaldhausen T.ι).kBasepoint
        (Fibration.changeWeakMap_basepoint (boundedAboveFlatPerfectSupportedOpenNested j T)) 0 a :=
  boundedAboveFlatPerfectSupportedUnionFiberKMap_connecting j T 0 a

example : IsIso ((stableHomotopyFunctor 0).map
    (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T)) :=
  boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence j T 0

example : IsIso ((stableHomotopyFunctor (-1)).map
    (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T)) :=
  boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence j T (-1)

example : Subsingleton (stableHomotopyGroup
    (homotopyFiber (Fibration.changeWeakPrespectrumMap
      (boundedAboveFlatPerfectSupportedOpenNested j T))) (-1)) :=
  Fibration.changeWeakPrespectrumFiber_neg_subsingleton
    (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
    (-1) (by decide)
