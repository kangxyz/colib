/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientInitialEvaluationConnecting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFineFiberConnecting

/-!
# The original initial connecting map in the fine Bass telescope

The original stage-zero inclusions preserve both arrows of the initial
coefficient localization sequence and every time of its prescribed null.
Postcomposition by the original coarse-to-full-open telescope restriction gives
the actual full-open telescope null. Consequently the intrinsic initial fiber
boundary maps to the existing signed fine localization boundary in every
integer degree, without changing either boundary or choosing a new null.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original supported inclusion gives the initial telescope's forgetful square. -/
theorem boundedAboveFlatCoefficientInitialTelescope_forget (a : Under R) :
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a ≫
        (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a =
      (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f 0).app a ≫
        (boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a :=
  (NatTrans.congr_app
    (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_forget f 0) a).symm

/-- The original ambient stage-zero face retains the coarse-to-full-open restriction. -/
theorem boundedAboveFlatCoefficientInitialTelescope_fullOpen (a : Under R) :
    (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a ≫
        (boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a =
      (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a ≫
        ((boundedAboveFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
          (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) := by
  change (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a ≫
      ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a ≫
        (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h ↦ h ≫ (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)
      (NatTrans.congr_app
        (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_open f 0) a)).trans
        (Category.assoc _ _ _))

/-- Every original initial null value survives the same inclusion and full-open restriction. -/
theorem boundedAboveFlatCoefficientInitialTelescope_fullOpenNull
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
        (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a).map n
        (((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n (t, x)) =
      ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level n
        (t, ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f 0).app a).map n x) := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The initial intrinsic boundary enters the existing fine boundary through the original maps. -/
theorem boundedAboveFlatCoefficientInitialConnecting_telescope (a : Under R) (d : ℤ) :
    let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d ≫
        (stableHomotopyFunctor d).map
          ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f 0).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((boundedAboveFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
            (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) ≫
        boundedAboveFlatCoefficientFineLocalizationConnecting f a d := by
  let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
  rw [boundedAboveFlatCoefficientFineLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
    ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
    ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a)
    ((boundedAboveFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
      (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)
    (boundedAboveFlatCoefficientInitialTelescope_forget f a)
    (boundedAboveFlatCoefficientInitialTelescope_fullOpen f a)
    (boundedAboveFlatCoefficientInitialTelescope_fullOpenNull f a) d

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-1276",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      CoefficientInitialTelescopeConnecting.lean:73"
    "adaptation" "Original stage-zero inclusions carry the initial boundary to the fine boundary"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientInitialConnecting_telescope
