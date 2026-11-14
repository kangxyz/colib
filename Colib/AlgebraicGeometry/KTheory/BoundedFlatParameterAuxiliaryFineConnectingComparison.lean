/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIntrinsicConnecting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryFiberConnecting

/-!
# Auxiliary current-to-G7 signed connecting comparison

The four original telescope comparisons give explicit stable group
isomorphisms from the current model to the fine model. The intrinsic
current boundary agrees with the existing cone-defined fine boundary
through these maps, at every integral Spec coefficient and integer degree.

The finite conjugating words are retained. This is a boundary comparison
for the specified null diagrams, not an identification of the original
Bass quotient class maps or a separately specified classical presentation.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryFineConnectingComparison.lean`, revision
  `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology
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

/-- The actual iterated-to-fine comparison preserves the original signed fine boundary. -/
@[reassoc]
theorem iterated_fine_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    iteratedConnecting f T a d ≫ (stableHomotopyFunctor d).map
        ((GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison f T).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((GlobalAuxiliaryParameterCoefficient.openTelescopeComparison f T).app a) ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((iteratedRestriction f.left T).app (specUnder.obj a))
        ((iteratedEnlargement f.left T).app (specUnder.obj a))
        ((iteratedNull f.left T).homotopy (specUnder.obj a)))) :=
    iteratedLift_spec_isStableEquivalence f T a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f
      T a d
  rw [boundedFlatCoefficientAuxiliaryLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((iteratedEnlargement f.left T).app (specUnder.obj a))
    ((iteratedRestriction f.left T).app (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((iteratedNull f.left T).homotopy (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)
    ((GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison f T).app a)
    ((GlobalAuxiliaryParameterCoefficient.ambientTelescopeComparison Q T).app a)
    ((GlobalAuxiliaryParameterCoefficient.openTelescopeComparison f T).app a)
    (congrArg (fun η => η.app a)
      (GlobalAuxiliaryParameterCoefficient.telescope_enlargement_square f T))
    (congrArg (fun η => η.app a)
      (GlobalAuxiliaryParameterCoefficient.telescope_restriction_square f T)).symm
    (GlobalAuxiliaryParameterCoefficient.telescope_fullNull_square f T a) d

/-- The supported comparison retains the two forward maps, inverse iterated comparison, and
original fine evaluation, in that order. -/
def currentFineSupportComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (fiberAction f.left T)).obj (specUnder.obj a)) d ≅
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a) d := by
  let H := stableHomotopyFunctor d
  let e := (telescopeMap (fiberAction f.left T)).app (specUnder.obj a)
  let q := (conjugacyTelescopeMap (fiberAction f.left T)).app (specUnder.obj a)
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (fiberAction f.left T)).app (specUnder.obj a)
  let v := (GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison f T).app a
  let : IsIso (H.map e) := model_telescopeMap_stable
    (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map q) := model_conjugacyTelescopeMap_stable
    (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map m) := SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
    (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map v) :=
    GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison_stable f T a d
  exact asIso (H.map e) ≪≫ asIso (H.map q) ≪≫ (asIso (H.map m)).symm ≪≫ asIso (H.map v)

/-- The full-open comparison follows the same four actual arrows on the original open object. -/
def currentFineOpenComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (openAction f.left T)).obj (specUnder.obj a)) d ≅
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) d := by
  let H := stableHomotopyFunctor d
  let e := (telescopeMap (openAction f.left T)).app (specUnder.obj a)
  let q := (conjugacyTelescopeMap (openAction f.left T)).app (specUnder.obj a)
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (openAction f.left T)).app (specUnder.obj a)
  let v := (GlobalAuxiliaryParameterCoefficient.openTelescopeComparison f T).app a
  let : IsIso (H.map e) := model_telescopeMap_stable
    (openModel f.left T) (openAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map q) := model_conjugacyTelescopeMap_stable
    (openModel f.left T) (openAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map m) := SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
    (openModel f.left T) (openAction f.left T) (specUnder.obj a) d
  let : IsIso (H.map v) :=
    GlobalAuxiliaryParameterCoefficient.openTelescopeComparison_stable f T a d
  exact asIso (H.map e) ≪≫ asIso (H.map q) ≪≫ (asIso (H.map m)).symm ≪≫ asIso (H.map v)

private theorem inverse_boundary_square {D : Type*} [Category* D]
    {I J S T : D} (δ : I ⟶ S) (δ' : J ⟶ T) (s : S ⟶ T) (o : I ⟶ J)
    [IsIso s] [IsIso o] (h : δ ≫ s = o ≫ δ') :
    δ' ≫ inv s = inv o ≫ δ := by
  apply (cancel_epi o).1
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- In every signed degree the actual current boundary agrees through the unchanged zigzag
with the original fine cone boundary. No permutation acts as identity by assumption. -/
@[reassoc]
theorem current_fine_connecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f T a d ≫ (currentFineSupportComparison f T a d).hom =
      (currentFineOpenComparison f T a (d + 1)).hom ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d := by
  let mS := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (fiberAction f.left T)).app (specUnder.obj a)
  let mO := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
    (openAction f.left T)).app (specUnder.obj a)
  let : IsIso ((stableHomotopyFunctor d).map mS) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) d
  let : IsIso ((stableHomotopyFunctor (d + 1)).map mO) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (openModel f.left T) (openAction f.left T) (specUnder.obj a) (d + 1)
  have hI := inverse_boundary_square (iteratedConnecting f T a d) (twistedConnecting f T a d)
    ((stableHomotopyFunctor d).map mS) ((stableHomotopyFunctor (d + 1)).map mO)
    (iterated_twisted_connecting f T a d)
  have hI' := congrArg (fun k => k ≫ (stableHomotopyFunctor d).map
    ((GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison f T).app a)) hI
  simp only [Category.assoc] at hI'
  change currentConnecting f T a d ≫
      ((stableHomotopyFunctor d).map
        ((telescopeMap (fiberAction f.left T)).app (specUnder.obj a)) ≫
      (stableHomotopyFunctor d).map
        ((conjugacyTelescopeMap (fiberAction f.left T)).app (specUnder.obj a)) ≫
      inv ((stableHomotopyFunctor d).map mS) ≫
      (stableHomotopyFunctor d).map
        ((GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison f T).app a)) =
    ((stableHomotopyFunctor (d + 1)).map
        ((telescopeMap (openAction f.left T)).app (specUnder.obj a)) ≫
      (stableHomotopyFunctor (d + 1)).map
        ((conjugacyTelescopeMap (openAction f.left T)).app (specUnder.obj a)) ≫
      inv ((stableHomotopyFunctor (d + 1)).map mO) ≫
      (stableHomotopyFunctor (d + 1)).map
        ((GlobalAuxiliaryParameterCoefficient.openTelescopeComparison f T).app a)) ≫
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d
  simp only [← Category.assoc]
  rw [current_normalized_connecting]
  simp only [Category.assoc]
  rw [normalized_twisted_connecting_assoc, hI']
  rw [iterated_fine_connecting]

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

