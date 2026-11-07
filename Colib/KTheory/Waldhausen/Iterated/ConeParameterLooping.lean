/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConeParameterLoopingExcision
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity
public import Colib.KTheory.Waldhausen.Iterated.PointHEP

/-!
# Loop-cofiber comparison for actual iterated-S models

Every original morphism between the actual model prespectra has stable loop-cofiber
comparison. The genuine original S-level growth, all-point coverage, T1 topology, and literal
chosen-point HEP discharge both excision inputs, including the looped chosen point.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/ConeParameterLooping.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual native iterated-S prespectra on the strict chosen-zero wide subcategory
discharge the original point, separation and all-point finite connectivity premises. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open Topology SmallWaldhausenCategory
variable {W V : WideSubcategory preservesZero.{u}} (f : prespectrum W ⟶ prespectrum V)

/-- Every original map between actual models has genuine stable excision after parameter looping.
-/
theorem parameterLoopingMap_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) :=
  parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth f 0
    (prespectrum_point_homotopyExtensionProperty W)
    (prespectrum_point_homotopyExtensionProperty V)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at W (n + 1) k
      (by omega) x)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at V (n + 1) k
      (by omega) x)

/-- The unchanged original loop-cofiber comparison is stable with no additional model premises. -/
theorem mappingConeParameterLoopingComparison_isStableEquivalence :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth f 0
    (prespectrum_point_homotopyExtensionProperty W)
    (prespectrum_point_homotopyExtensionProperty V)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at W (n + 1) k
      (by omega) x)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at V (n + 1) k
      (by omega) x)

attribute [colib_tag "COL-0295"] parameterLoopingMap_coneFiber_isStableEquivalence
  mappingConeParameterLoopingComparison_isStableEquivalence

attribute [colib_ref "HatcherAT"
  "Section 4.2, Theorem 4.23, p. 360; proof, pp. 361-363" "background"
  "Classical CW-pair homotopy excision is background for the finite-connectivity argument;
    the actual loop-cofiber map, whole cylinder and signed stable comparison are proved here"]
  parameterLoopingMap_coneFiber_isStableEquivalence
  mappingConeParameterLoopingComparison_isStableEquivalence

attribute [colib_ref "ThomasonTrobaugh1990" "Section 1.5.3, p. 260" "background"
  "The original K-spectrum is the application here; linear growth and chosen-point HEP
    separately prove stability of this literal loop-cofiber comparison"]
  mappingConeParameterLoopingComparison_isStableEquivalence

end CategoryTheory.Waldhausen.IteratedS
