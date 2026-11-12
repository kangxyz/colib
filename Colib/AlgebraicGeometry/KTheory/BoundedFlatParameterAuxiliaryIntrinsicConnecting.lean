/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization
public import Colib.Topology.Prespectrum.FiberLiftConnecting

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryIntrinsicConnecting.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Intrinsic signed boundaries of the auxiliary-supported parameter telescopes

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
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open KTheory.Bass.SchemeNaturalSeed

universe u

namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The boundary of the original current-stage null at an actual integral Spec coefficient. -/
def currentConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (openAction f.left T)).obj (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup ((currentTelescope (fiberAction f.left T)).obj (specUnder.obj a)) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentRestriction f.left T).app (specUnder.obj a))
        ((currentEnlargement f.left T).app (specUnder.obj a))
        ((currentNull f.left T).homotopy (specUnder.obj a)))) :=
    currentLift_spec_isStableEquivalence f T a d
  exact stableFiberLiftConnecting ((currentEnlargement f.left T).app (specUnder.obj a))
    ((currentRestriction f.left T).app (specUnder.obj a))
    ((currentNull f.left T).homotopy (specUnder.obj a)) d

/-- The boundary of the original iterated-seed null, without any replacement track. -/
def iteratedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((iteratedTelescope (openAction f.left T)).obj (specUnder.obj a))
        (d + 1) ⟶
      stableHomotopyGroup ((iteratedTelescope (fiberAction f.left T)).obj (specUnder.obj a))
        d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedRestriction f.left T).app (specUnder.obj a))
        ((iteratedEnlargement f.left T).app (specUnder.obj a))
        ((iteratedNull f.left T).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f T a d
  exact stableFiberLiftConnecting ((iteratedEnlargement f.left T).app (specUnder.obj a))
    ((iteratedRestriction f.left T).app (specUnder.obj a))
    ((iteratedNull f.left T).homotopy (specUnder.obj a)) d

/-- The boundary of the original unpermuted normalized null. -/
def normalizedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((normalizedTelescope (openAction f.left T)).obj (specUnder.obj a))
        (d + 1) ⟶
      stableHomotopyGroup ((normalizedTelescope (fiberAction f.left T)).obj (specUnder.obj a))
        d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedRestriction f.left T).app (specUnder.obj a))
        ((normalizedEnlargement f.left T).app (specUnder.obj a))
        ((normalizedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left T (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f T a)) d
  exact stableFiberLiftConnecting ((normalizedEnlargement f.left T).app (specUnder.obj a))
    ((normalizedRestriction f.left T).app (specUnder.obj a))
    ((normalizedNull f.left T).homotopy (specUnder.obj a)) d

/-- The boundary of the specified twisted null, retaining the actual finite words. -/
def twistedConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((twistedTelescope (openAction f.left T)).obj (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup ((twistedTelescope (fiberAction f.left T)).obj (specUnder.obj a)) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedRestriction f.left T).app (specUnder.obj a))
        ((twistedEnlargement f.left T).app (specUnder.obj a))
        ((twistedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left T (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f T a)) d
  exact stableFiberLiftConnecting ((twistedEnlargement f.left T).app (specUnder.obj a))
    ((twistedRestriction f.left T).app (specUnder.obj a))
    ((twistedNull f.left T).homotopy (specUnder.obj a)) d

/-- The original current-to-normalized comparison preserves the signed connecting map. -/
@[reassoc]
theorem current_normalized_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f T a d ≫ (stableHomotopyFunctor d).map
        ((telescopeMap (fiberAction f.left T)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((telescopeMap (openAction f.left T)).app (specUnder.obj a)) ≫
        normalizedConnecting f T a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentRestriction f.left T).app (specUnder.obj a))
        ((currentEnlargement f.left T).app (specUnder.obj a))
        ((currentNull f.left T).homotopy (specUnder.obj a)))) :=
    currentLift_spec_isStableEquivalence f T a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedRestriction f.left T).app (specUnder.obj a))
        ((normalizedEnlargement f.left T).app (specUnder.obj a))
        ((normalizedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left T (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f T a)) d
  exact stableFiberLiftConnecting_naturality
    ((currentEnlargement f.left T).app (specUnder.obj a))
    ((currentRestriction f.left T).app (specUnder.obj a))
    ((normalizedEnlargement f.left T).app (specUnder.obj a))
    ((normalizedRestriction f.left T).app (specUnder.obj a))
    ((currentNull f.left T).homotopy (specUnder.obj a))
    ((normalizedNull f.left T).homotopy (specUnder.obj a))
    ((telescopeMap (fiberAction f.left T)).app (specUnder.obj a))
    ((telescopeMap (ambientAction T)).app (specUnder.obj a))
    ((telescopeMap (openAction f.left T)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (telescopeMap_input_square
      (fiberAction f.left T) (ambientAction T) _ (enlargement_equivariant f.left T)))
    (congrArg (fun η => η.app (specUnder.obj a)) (telescopeMap_input_square
      (ambientAction T) (openAction f.left T) _ (restriction_equivariant f.left T))).symm
    (current_null_square f.left T (specUnder.obj a)) d

/-- The actual finite-word conjugacy preserves the boundary without trivializing its words. -/
@[reassoc]
theorem normalized_twisted_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    normalizedConnecting f T a d ≫ (stableHomotopyFunctor d).map
        ((conjugacyTelescopeMap (fiberAction f.left T)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((conjugacyTelescopeMap (openAction f.left T)).app (specUnder.obj a)) ≫
        twistedConnecting f T a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((normalizedRestriction f.left T).app (specUnder.obj a))
        ((normalizedEnlargement f.left T).app (specUnder.obj a))
        ((normalizedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((current_normalized_lift_stable_iff f.left T (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f T a)) d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedRestriction f.left T).app (specUnder.obj a))
        ((twistedEnlargement f.left T).app (specUnder.obj a))
        ((twistedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left T (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f T a)) d
  exact stableFiberLiftConnecting_naturality
    ((normalizedEnlargement f.left T).app (specUnder.obj a))
    ((normalizedRestriction f.left T).app (specUnder.obj a))
    ((twistedEnlargement f.left T).app (specUnder.obj a))
    ((twistedRestriction f.left T).app (specUnder.obj a))
    ((normalizedNull f.left T).homotopy (specUnder.obj a))
    ((twistedNull f.left T).homotopy (specUnder.obj a))
    ((conjugacyTelescopeMap (fiberAction f.left T)).app (specUnder.obj a))
    ((conjugacyTelescopeMap (ambientAction T)).app (specUnder.obj a))
    ((conjugacyTelescopeMap (openAction f.left T)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (conjugacyTelescopeMap_input_square
      (fiberAction f.left T) (ambientAction T) _ (enlargement_equivariant f.left T)))
    (congrArg (fun η => η.app (specUnder.obj a)) (conjugacyTelescopeMap_input_square
      (ambientAction T) (openAction f.left T) _ (restriction_equivariant f.left T))).symm
    (twisted_null_square f.left T (specUnder.obj a)) d

/-- The original iterated-seed comparison preserves the signed boundary of the same whole null. -/
@[reassoc]
theorem iterated_twisted_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    iteratedConnecting f T a d ≫ (stableHomotopyFunctor d).map
        ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
          (fiberAction f.left T)).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
            (openAction f.left T)).app (specUnder.obj a)) ≫
        twistedConnecting f T a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedRestriction f.left T).app (specUnder.obj a))
        ((iteratedEnlargement f.left T).app (specUnder.obj a))
        ((iteratedNull f.left T).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f T a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((twistedRestriction f.left T).app (specUnder.obj a))
        ((twistedEnlargement f.left T).app (specUnder.obj a))
        ((twistedNull f.left T).homotopy (specUnder.obj a)))) :=
    ((iterated_twisted_lift_stable_iff f.left T (specUnder.obj a)).mp
    (iteratedLift_spec_isStableEquivalence f T a)) d
  exact stableFiberLiftConnecting_naturality
    ((iteratedEnlargement f.left T).app (specUnder.obj a))
    ((iteratedRestriction f.left T).app (specUnder.obj a))
    ((twistedEnlargement f.left T).app (specUnder.obj a))
    ((twistedRestriction f.left T).app (specUnder.obj a))
    ((iteratedNull f.left T).homotopy (specUnder.obj a))
    ((twistedNull f.left T).homotopy (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (fiberAction f.left T)).app (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (ambientAction T)).app (specUnder.obj a))
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
      (openAction f.left T)).app (specUnder.obj a))
    (congrArg (fun η => η.app (specUnder.obj a)) (SchemeIteratedSeedTelescope.input_square
      (fiberAction f.left T) (ambientAction T) _ (enlargement_equivariant f.left T)))
    (congrArg (fun η => η.app (specUnder.obj a)) (SchemeIteratedSeedTelescope.input_square
      (ambientAction T) (openAction f.left T) _ (restriction_equivariant f.left T))).symm
    (fun n r x => SchemeIteratedSeedTelescope.null_square
      (fiberAction f.left T) (ambientAction T) (openAction f.left T) _ _
      (enlargement_equivariant f.left T) (restriction_equivariant f.left T)
      (fullNull f.left T) (timeSlice_equivariant f.left T) (specUnder.obj a) n r x) d

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
