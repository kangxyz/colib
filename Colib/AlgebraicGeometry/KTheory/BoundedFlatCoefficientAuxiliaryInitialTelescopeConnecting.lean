/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryInitialConnecting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryFiberConnecting

/-!
# The original initial connecting map in the auxiliary-support Bass telescope

The original stage-zero inclusions preserve both arrows of the initial
auxiliary-supported localization sequence and every time of its prescribed null.
Postcomposition by the original coarse-to-full-open telescope restriction gives
the actual full-open telescope null. Consequently the intrinsic initial fiber
boundary maps to the existing signed auxiliary localization boundary in every
integer degree, without changing either boundary or choosing a new null.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original supported inclusion gives the initial telescope's forgetful square. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialTelescope_forget (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a =
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a :=
  (NatTrans.congr_app
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion_forget f T 0) a).symm

omit [IsOpenImmersion f.left] in
/-- The original ambient stage-zero face retains the coarse-to-full-open restriction. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialTelescope_fullOpen (a : Under R) :
    (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a ≫
        (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a ≫
        ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
          (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) := by
  change (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a ≫
      ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h ↦
        h ≫ (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)
      (NatTrans.congr_app
        (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_open f T 0) a)).trans
        (Category.assoc _ _ _))

/-- Every original initial null value survives the same inclusion and full-open restriction. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialTelescope_fullOpenNull
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map n
        (((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n
          (t, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (t, ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app
          a).map n x) :=
  rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- The initial intrinsic boundary enters the existing fine boundary through the original maps. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialConnecting_telescope (a : Under R) (d : ℤ) :
    let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d ≫
        (stableHomotopyFunctor d).map
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
            (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d := by
  let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
      f T a d
  rw [boundedFlatCoefficientAuxiliaryLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
    ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
    ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
      (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)
    (boundedAboveFlatCoefficientAuxiliaryInitialTelescope_forget f T a)
    (boundedAboveFlatCoefficientAuxiliaryInitialTelescope_fullOpen f T a)
    (boundedAboveFlatCoefficientAuxiliaryInitialTelescope_fullOpenNull f T a) d

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-1276",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      CoefficientAuxiliaryInitialTelescopeConnecting.lean:77"
    "adaptation" "Actual auxiliary stage-zero inclusions carry the same null and signed boundary"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientAuxiliaryInitialConnecting_telescope
