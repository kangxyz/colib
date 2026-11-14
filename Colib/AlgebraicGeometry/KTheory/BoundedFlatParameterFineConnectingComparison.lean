/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIntrinsicConnecting
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFineFiberConnecting

/-!
# The actual current-to-fine comparison preserves the signed boundary

The four original telescope comparisons give explicit stable group
isomorphisms from the current model to the fine model. The intrinsic
current boundary agrees with the existing cone-defined fine boundary
through these maps, at every integral Spec coefficient and integer degree.

The finite conjugating words are retained. This is a boundary comparison
for the specified null diagrams, not an identification of the original
Bass quotient class maps or a separately specified classical presentation.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open KTheory.Bass.SchemeNaturalSeed

universe u

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

open GlobalSupportedSection

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The actual iterated-to-fine comparison preserves the original signed fine boundary. -/
@[reassoc]
theorem iterated_fine_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    iteratedConnecting f a d ≫ (stableHomotopyFunctor d).map
        ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((GlobalParameterCoefficient.fineTelescopeComparison P).app a) ≫
        boundedAboveFlatCoefficientFineLocalizationConnecting f a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedOpen f.left).app (specUnder.obj a))
        ((iteratedForget f.left).app (specUnder.obj a))
        ((iteratedNull f.left).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
  rw [boundedAboveFlatCoefficientFineLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((iteratedForget f.left).app (specUnder.obj a))
    ((iteratedOpen f.left).app (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((iteratedNull f.left).homotopy (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a)
    ((GlobalParameterCoefficient.fineTelescopeComparison Q).app a)
    ((GlobalParameterCoefficient.fineTelescopeComparison P).app a)
    (congrArg (fun η => η.app a)
      (GlobalSupportedParameterCoefficient.fineTelescope_forget_square f))
    (congrArg (fun η => η.app a) (iteratedOpen_fine_square f)).symm
    (GlobalParameterCoefficient.telescope_fullNull_fine_square f a) d

set_option maxHeartbeats 600000 in
-- The four exact stable comparison maps retain the actual finite transports.
/-- The supported comparison retains the two forward maps, inverse iterated comparison, and
original fine evaluation, in that order. -/
def currentFineSupportComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (supportedTrack f.left)).obj (specUnder.obj a)) d ≅
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).obj a) d := by
  let H := stableHomotopyFunctor d
  let e := (telescopeMap (supportedTrack f.left)).app (specUnder.obj a)
  let q := (conjugacyTelescopeMap (supportedTrack f.left)).app (specUnder.obj a)
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (supportedTrack f.left)).app (specUnder.obj a)
  let v := (GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a
  let : IsIso (H.map e) := model_telescopeMap_stable
    (ParameterModels.supported f.left) (supportedTrack f.left) (specUnder.obj a) d
  let : IsIso (H.map q) := model_conjugacyTelescopeMap_stable
    (ParameterModels.supported f.left) (supportedTrack f.left) (specUnder.obj a) d
  let : IsIso (H.map m) := SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
    (ParameterModels.supported f.left) (supportedTrack f.left) (specUnder.obj a) d
  let : IsIso (H.map v) :=
    GlobalSupportedParameterCoefficient.fineTelescopeComparison_stable f a d
  exact asIso (H.map e) ≪≫ asIso (H.map q) ≪≫ (asIso (H.map m)).symm ≪≫ asIso (H.map v)

set_option maxHeartbeats 600000 in
-- The four exact stable comparison maps retain the actual finite transports.
/-- The full-open comparison follows the same four actual arrows on the original open object. -/
def currentFineOpenComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (ambientTrack P.left)).obj (specUnder.obj a)) d ≅
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) d := by
  let H := stableHomotopyFunctor d
  let e := (telescopeMap (ambientTrack P.left)).app (specUnder.obj a)
  let q := (conjugacyTelescopeMap (ambientTrack P.left)).app (specUnder.obj a)
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (ambientTrack P.left)).app (specUnder.obj a)
  let v := (GlobalParameterCoefficient.fineTelescopeComparison P).app a
  let : IsIso (H.map e) := model_telescopeMap_stable
    (ParameterModels.ambient P.left) (ambientTrack P.left) (specUnder.obj a) d
  let : IsIso (H.map q) := model_conjugacyTelescopeMap_stable
    (ParameterModels.ambient P.left) (ambientTrack P.left) (specUnder.obj a) d
  let : IsIso (H.map m) := SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
    (ParameterModels.ambient P.left) (ambientTrack P.left) (specUnder.obj a) d
  let : IsIso (H.map v) := GlobalParameterCoefficient.fineTelescopeComparison_stable P a d
  exact asIso (H.map e) ≪≫ asIso (H.map q) ≪≫ (asIso (H.map m)).symm ≪≫ asIso (H.map v)

private theorem inverse_boundary_square {D : Type*} [Category* D]
    {I J S T : D} (δ : I ⟶ S) (δ' : J ⟶ T) (s : S ⟶ T) (o : I ⟶ J)
    [IsIso s] [IsIso o] (h : δ ≫ s = o ≫ δ') :
    δ' ≫ inv s = inv o ≫ δ := by
  apply (cancel_epi o).1
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

set_option maxHeartbeats 600000 in
-- The comparison uses the full actual telescope zigzag in both degrees.
/-- In every signed degree the actual current boundary agrees through the unchanged zigzag
with the original fine cone boundary. No permutation acts as identity by assumption. -/
@[reassoc]
theorem current_fine_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f a d ≫ (currentFineSupportComparison f a d).hom =
      (currentFineOpenComparison f a (d + 1)).hom ≫
        boundedAboveFlatCoefficientFineLocalizationConnecting f a d := by
  let mS := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (supportedTrack f.left)).app (specUnder.obj a)
  let mO := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (ambientTrack P.left)).app (specUnder.obj a)
  let : IsIso ((stableHomotopyFunctor d).map mS) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.supported f.left) (supportedTrack f.left) (specUnder.obj a) d
  let : IsIso ((stableHomotopyFunctor (d + 1)).map mO) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.ambient P.left) (ambientTrack P.left) (specUnder.obj a) (d + 1)
  have hI := inverse_boundary_square (iteratedConnecting f a d) (twistedConnecting f a d)
    ((stableHomotopyFunctor d).map mS) ((stableHomotopyFunctor (d + 1)).map mO)
    (iterated_twisted_connecting f a d)
  have hI' := congrArg (fun k => k ≫ (stableHomotopyFunctor d).map
    ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a)) hI
  simp only [Category.assoc] at hI'
  change currentConnecting f a d ≫
      ((stableHomotopyFunctor d).map
        ((telescopeMap (supportedTrack f.left)).app (specUnder.obj a)) ≫
      (stableHomotopyFunctor d).map
        ((conjugacyTelescopeMap (supportedTrack f.left)).app (specUnder.obj a)) ≫
      inv ((stableHomotopyFunctor d).map mS) ≫
      (stableHomotopyFunctor d).map
        ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a)) =
    ((stableHomotopyFunctor (d + 1)).map
        ((telescopeMap (ambientTrack P.left)).app (specUnder.obj a)) ≫
      (stableHomotopyFunctor (d + 1)).map
        ((conjugacyTelescopeMap (ambientTrack P.left)).app (specUnder.obj a)) ≫
      inv ((stableHomotopyFunctor (d + 1)).map mO) ≫
      (stableHomotopyFunctor (d + 1)).map
        ((GlobalParameterCoefficient.fineTelescopeComparison P).app a)) ≫
      boundedAboveFlatCoefficientFineLocalizationConnecting f a d
  simp only [← Category.assoc]
  rw [current_normalized_connecting]
  simp only [Category.assoc]
  rw [normalized_twisted_connecting_assoc, hI']
  rw [iterated_fine_connecting]

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

