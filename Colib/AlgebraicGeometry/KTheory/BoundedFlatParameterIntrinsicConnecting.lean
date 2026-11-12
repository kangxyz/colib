/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber
public import Colib.Topology.Prespectrum.FiberLiftConnecting

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIntrinsicConnecting.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Intrinsic signed boundaries of the four actual parameter telescopes

The original iterated, current, normalized and twisted null diagrams each
supply their signed fiber-lift boundary. Their actual comparison maps
preserve these boundaries in every integer degree. All lift isomorphisms
are supplied by the proved localization theorem under the original
compactness hypotheses; no class-map or permutation-sign identification
is assumed.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Topology
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open KTheory.Bass.SchemeNaturalSeed

universe u

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The boundary of the original current-stage null at an actual integral Spec coefficient. -/
def currentConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (ambientTrack P.left)).obj (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup ((currentTelescope (supportedTrack f.left)).obj (specUnder.obj a)) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentOpen f.left).app (specUnder.obj a))
        ((currentForget f.left).app (specUnder.obj a))
        ((currentNull f.left).homotopy (specUnder.obj a)))) :=
    currentLift_spec_isStableEquivalence f a d
  exact stableFiberLiftConnecting ((currentForget f.left).app (specUnder.obj a))
    ((currentOpen f.left).app (specUnder.obj a))
    ((currentNull f.left).homotopy (specUnder.obj a)) d

/-- The boundary of the original iterated-seed null, without any replacement track. -/
def iteratedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((iteratedTelescope (ambientTrack P.left)).obj (specUnder.obj a))
        (d + 1) ⟶
      stableHomotopyGroup ((iteratedTelescope (supportedTrack f.left)).obj (specUnder.obj a))
        d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedOpen f.left).app (specUnder.obj a))
        ((iteratedForget f.left).app (specUnder.obj a))
        ((iteratedNull f.left).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f a d
  exact stableFiberLiftConnecting ((iteratedForget f.left).app (specUnder.obj a))
    ((iteratedOpen f.left).app (specUnder.obj a))
    ((iteratedNull f.left).homotopy (specUnder.obj a)) d

/-- The boundary of the original unpermuted normalized null. -/
def normalizedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((normalizedTelescope (ambientTrack P.left)).obj (specUnder.obj a))
        (d + 1) ⟶
      stableHomotopyGroup ((normalizedTelescope (supportedTrack f.left)).obj (specUnder.obj a))
        d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedOpen f.left).app (specUnder.obj a))
        ((normalizedForget f.left).app (specUnder.obj a))
        ((normalizedNull f.left).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f a)) d
  exact stableFiberLiftConnecting ((normalizedForget f.left).app (specUnder.obj a))
    ((normalizedOpen f.left).app (specUnder.obj a))
    ((normalizedNull f.left).homotopy (specUnder.obj a)) d

/-- The boundary of the specified twisted null, retaining the actual finite words. -/
def twistedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((twistedTelescope (ambientTrack P.left)).obj (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup ((twistedTelescope (supportedTrack f.left)).obj (specUnder.obj a)) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedOpen f.left).app (specUnder.obj a))
        ((twistedForget f.left).app (specUnder.obj a))
        ((twistedNull f.left).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f a)) d
  exact stableFiberLiftConnecting ((twistedForget f.left).app (specUnder.obj a))
    ((twistedOpen f.left).app (specUnder.obj a))
    ((twistedNull f.left).homotopy (specUnder.obj a)) d

/-- The original current-to-normalized comparison preserves the signed connecting map. -/
@[reassoc]
theorem current_normalized_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f a d ≫ (stableHomotopyFunctor d).map
        ((telescopeMap (supportedTrack f.left)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((telescopeMap (ambientTrack P.left)).app (specUnder.obj a)) ≫
        normalizedConnecting f a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentOpen f.left).app (specUnder.obj a))
        ((currentForget f.left).app (specUnder.obj a))
        ((currentNull f.left).homotopy (specUnder.obj a)))) :=
    currentLift_spec_isStableEquivalence f a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedOpen f.left).app (specUnder.obj a))
        ((normalizedForget f.left).app (specUnder.obj a))
        ((normalizedNull f.left).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f a)) d
  exact stableFiberLiftConnecting_naturality
    ((currentForget f.left).app (specUnder.obj a))
    ((currentOpen f.left).app (specUnder.obj a))
    ((normalizedForget f.left).app (specUnder.obj a))
    ((normalizedOpen f.left).app (specUnder.obj a))
    ((currentNull f.left).homotopy (specUnder.obj a))
    ((normalizedNull f.left).homotopy (specUnder.obj a))
    ((telescopeMap (supportedTrack f.left)).app (specUnder.obj a))
    ((telescopeMap (ambientTrack Q.left)).app (specUnder.obj a))
    ((telescopeMap (ambientTrack P.left)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (telescopeMap_input_square
      (supportedTrack f.left) (ambientTrack Q.left) _ (forget_equivariant f.left)))
    (congrArg (fun η => η.app (specUnder.obj a)) (telescopeMap_input_square
      (ambientTrack Q.left) (ambientTrack P.left) _ (fullMap_equivariant f.left))).symm
    (current_null_square f.left (specUnder.obj a)) d

/-- The actual finite-word conjugacy preserves the boundary without trivializing its words. -/
@[reassoc]
theorem normalized_twisted_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    normalizedConnecting f a d ≫ (stableHomotopyFunctor d).map
        ((conjugacyTelescopeMap (supportedTrack f.left)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((conjugacyTelescopeMap (ambientTrack P.left)).app (specUnder.obj a)) ≫
        twistedConnecting f a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedOpen f.left).app (specUnder.obj a))
        ((normalizedForget f.left).app (specUnder.obj a))
        ((normalizedNull f.left).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f a)) d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedOpen f.left).app (specUnder.obj a))
        ((twistedForget f.left).app (specUnder.obj a))
        ((twistedNull f.left).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f a)) d
  exact stableFiberLiftConnecting_naturality
    ((normalizedForget f.left).app (specUnder.obj a))
    ((normalizedOpen f.left).app (specUnder.obj a))
    ((twistedForget f.left).app (specUnder.obj a))
    ((twistedOpen f.left).app (specUnder.obj a))
    ((normalizedNull f.left).homotopy (specUnder.obj a))
    ((twistedNull f.left).homotopy (specUnder.obj a))
    ((conjugacyTelescopeMap (supportedTrack f.left)).app (specUnder.obj a))
    ((conjugacyTelescopeMap (ambientTrack Q.left)).app (specUnder.obj a))
    ((conjugacyTelescopeMap (ambientTrack P.left)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (conjugacyTelescopeMap_input_square
      (supportedTrack f.left) (ambientTrack Q.left) _ (forget_equivariant f.left)))
    (congrArg (fun η => η.app (specUnder.obj a)) (conjugacyTelescopeMap_input_square
      (ambientTrack Q.left) (ambientTrack P.left) _ (fullMap_equivariant f.left))).symm
    (twisted_null_square f.left (specUnder.obj a)) d

/-- The original iterated-seed comparison preserves the signed boundary of the same whole null. -/
@[reassoc]
theorem iterated_twisted_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    iteratedConnecting f a d ≫ (stableHomotopyFunctor d).map
        ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
          (supportedTrack f.left)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
            (ambientTrack P.left)).app (specUnder.obj a)) ≫
        twistedConnecting f a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedOpen f.left).app (specUnder.obj a))
        ((iteratedForget f.left).app (specUnder.obj a))
        ((iteratedNull f.left).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedOpen f.left).app (specUnder.obj a))
        ((twistedForget f.left).app (specUnder.obj a))
        ((twistedNull f.left).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f a)) d
  exact stableFiberLiftConnecting_naturality
    ((iteratedForget f.left).app (specUnder.obj a))
    ((iteratedOpen f.left).app (specUnder.obj a))
    ((twistedForget f.left).app (specUnder.obj a))
    ((twistedOpen f.left).app (specUnder.obj a))
    ((iteratedNull f.left).homotopy (specUnder.obj a))
    ((twistedNull f.left).homotopy (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (supportedTrack f.left)).app (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (ambientTrack Q.left)).app (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (ambientTrack P.left)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (SchemeIteratedSeedTelescope.input_square
      (supportedTrack f.left) (ambientTrack Q.left) _ (forget_equivariant f.left)))
    (congrArg (fun η => η.app (specUnder.obj a)) (SchemeIteratedSeedTelescope.input_square
      (ambientTrack Q.left) (ambientTrack P.left) _ (fullMap_equivariant f.left))).symm
    (fun n r x => SchemeIteratedSeedTelescope.null_square
      (supportedTrack f.left) (ambientTrack Q.left) (ambientTrack P.left) _ _
      (forget_equivariant f.left) (fullMap_equivariant f.left)
      (fullNull f.left) (timeSlice_equivariant f.left) (specUnder.obj a) n r x) d

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
