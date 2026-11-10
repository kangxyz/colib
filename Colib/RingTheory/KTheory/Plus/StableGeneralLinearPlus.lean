/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.PlusConstruction.Basic
public import Colib.Topology.ClassifyingSpace.StableProjectiveLocalHomology
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionKernel
public import Colib.Topology.Realization.Connectivity

/-!
# Plus certification of the independent ring-specific completion model

The original stable map to the zero component of the independently constructed
projective group completion has the original stable elementary kernel and
preserves every target local system in universe `u + 1`. These already-proved
properties certify it in the explicit homological sense of `IsPlusConstruction`.
No CW existence/uniqueness theorem or identification of the homotopy fiber's
ordinary homology is assumed by this certificate.
-/

@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u
namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original stable elementary subgroup inside the actual source fundamental group. -/
def stableElementaryPiOneSubgroup :
    Subgroup (HomotopyGroup.Pi 1
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) (stableBase R)) :=
  (StableGeneralLinear.elementary R).map
    (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom

/-- Perfectness is inherited from the genuinely proved stable elementary group. -/
theorem stableElementaryPiOneSubgroup_isPerfect :
    Group.IsPerfect (stableElementaryPiOneSubgroup R) :=
  Group.IsPerfect.map _

/-- The general based map is literally the originally constructed stable based map. -/
theorem basedPiOneMap_stableZeroMap :
    basedPiOneMap (stableZeroMap R) (basepointPath R) = stablePiOneMap R := rfl

/-- Every property of this ring-specific plus certificate has been proved for the
original stable map, including arbitrary target local systems in the stated universe. -/
theorem stableZeroMap_isPlusConstruction :
    IsPlusConstruction.{u, u + 1, u + 1} (stableZeroMap R) (basepointPath R)
      (stableElementaryPiOneSubgroup R) where
  sourcePathConnected := inferInstance
  targetPathConnected := isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  perfect := stableElementaryPiOneSubgroup_isPerfect R
  surjective := stablePiOneMap_surjective R
  kernelEq := ker_stablePiOneMap R
  localCoefficients := StableFreeRight.stableZeroMap_localCoefficients_quasiIso R


attribute [colib_ref "quillen"
  "Quillen/KTheory/Plus/StableGeneralLinearPlus.lean:31-36"
  "adaptation" "All rings and the original stable map, basepoint path and full local systems"]
  stableElementaryPiOneSubgroup

attribute [colib_ref "quillen"
  "Quillen/KTheory/Plus/StableGeneralLinearPlus.lean:38-41"
  "adaptation" "All rings and the original stable map, basepoint path and full local systems"]
  stableElementaryPiOneSubgroup_isPerfect

attribute [colib_ref "quillen"
  "Quillen/KTheory/Plus/StableGeneralLinearPlus.lean:43-45"
  "adaptation" "All rings and the original stable map, basepoint path and full local systems"]
  basedPiOneMap_stableZeroMap

attribute [colib_ref "quillen"
  "Quillen/KTheory/Plus/StableGeneralLinearPlus.lean:47-57"
  "adaptation" "All rings and the original stable map, basepoint path and full local systems"]
  stableZeroMap_isPlusConstruction

attribute [colib_tag "COL-0513"]
  stableZeroMap_isPlusConstruction

end ModuleCat.FiniteProjective.StableCompletion
