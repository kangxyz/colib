/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedUnionPrespectrum

/-! Consumers retain the actual support, chosen-zero normalization and complete paths.
There are no compactness hypotheses. Natural degree zero and arbitrary integer degrees
are tested separately; the coarse connective fiber is not a Bass localization claim. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum
open scoped unitInterval

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example : Function.Bijective (boundedAboveFlatPerfectSupportedUnionFiberKMap j T 0) :=
  boundedAboveFlatPerfectSupportedUnionFiberKMap_bijective j T 0

example (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom =
      KMap (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T) n :=
  boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inverse j T n

example (n : ℕ) (a : BoundedAboveFlatPerfectSupportedOpenK j T (n + 1)) :
    boundedAboveFlatPerfectSupportedUnionFiberKMap j T n
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T n a) =
      HomotopyFiber.connectingHom
        (Fibration.changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
        (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint
        (boundedAboveFlatPerfectSupportedWaldhausen T.ι).kBasepoint
        (Fibration.changeWeakMap_basepoint (boundedAboveFlatPerfectSupportedOpenNested j T)) n a :=
  boundedAboveFlatPerfectSupportedUnionFiberKMap_connecting j T n a

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map
    (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T)) :=
  boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence j T d

example :
    boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j T)) =
      boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        Fibration.acyclicInclusionPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j T) :=
  boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_projection j T

example (n : ℕ)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).space n)
    (s : unitInterval) :
    ((boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T).map n x).1.2 s =
      (Fibration.acyclicPrespectrumNullhomotopy
        (boundedAboveFlatPerfectSupportedOpenNested j T)).level n
          (s, (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T).map n x) :=
  boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_path j T n x s

example (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).space n) :
    (boundedAboveFlatPerfectSupportedUnionRebasedNullhomotopy j T).level (n + 1)
        (s, (originalPrespectrum
          (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).structureMap n x t) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedOpenWaldhausen j T)).structureMap n
        ((boundedAboveFlatPerfectSupportedUnionRebasedNullhomotopy j T).level n (s, x)) t :=
  (boundedAboveFlatPerfectSupportedUnionRebasedNullhomotopy j T).comm n s x t

example (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatPerfectSupportedUnionInclusionNullhomotopy j T).level n
        (s, (originalPrespectrum
          (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).point n) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedOpenWaldhausen j T)).point n :=
  (boundedAboveFlatPerfectSupportedUnionInclusionNullhomotopy j T).at_point n s

example (n : ℕ)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).space n) :
    (boundedAboveFlatPerfectSupportedUnionProjectionHomotopy j T).level n (1, x) =
      (boundedAboveFlatPerfectSupportedUnionInclusionPrespectrumMap j T).map n x :=
  (boundedAboveFlatPerfectSupportedUnionProjectionHomotopy j T).at_one n x
