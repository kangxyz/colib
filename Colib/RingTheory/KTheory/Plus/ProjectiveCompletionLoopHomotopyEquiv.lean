/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.LoopDomination
public import Colib.Topology.Realization.Domination
public import Colib.Topology.Homotopy.Equiv.PathComponent
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZeroLoops
public import Colib.RingTheory.KTheory.Plus.StableGeneralLinearPlus

/-!
# Exact-forward homotopy equivalences for the standard original Q comparison

Constructed loop realization domination upgrades the already-proved weak
equivalence. The standard forward map is preserved definitionally. Restriction
to the original zero component retains the exact standard zero comparison and
its prescribed basepoint track. The source is the independently constructed
completion model already certified as a BGL-plus target for stableZeroMap.
No homotopy inverse or component equivalence is assumed.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionLoopHomotopyEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology Simplicial
universe u
namespace ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]

/-- The exact standard completion comparison, upgraded by the actual constructed domination. -/
def completionToOriginalQLoopsHomotopyEquiv (U : GroupCompletionCategory R) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (GroupCompletionCategory R))
      (Path (classifyingSpacePoint (exactStructure.{u, u} R).qZero)
        (classifyingSpacePoint (exactStructure.{u, u} R).qZero)) :=
  let D := RankedChainOrder.universalLoopDominationData
    (exactStructure.{u, u} R).QCategory (exactStructure R).qZero
  Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination
    (completionToOriginalQLoops R U) (completionToOriginalQLoops_isWeakHomotopyEquivalence R U)
    D.1 D.2.1 D.2.2.1 D.2.2.2

/-- The upgraded forward map is literally the fixed standard comparison. -/
theorem completionToOriginalQLoopsHomotopyEquiv_toFun (U : GroupCompletionCategory R) :
    (completionToOriginalQLoopsHomotopyEquiv R U).toFun =
      completionToOriginalQLoops R U := rfl

/-- The canonical additive-zero-pair comparison has the exact same forward map after upgrade. -/
def originalQComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (GroupCompletionCategory R))
      (Path (classifyingSpacePoint (exactStructure.{u, u} R).qZero)
        (classifyingSpacePoint (exactStructure.{u, u} R).qZero)) :=
  completionToOriginalQLoopsHomotopyEquiv R (completionZeroPair R)

/-- No inverse, reversal, or relabeling replaces the standard original comparison. -/
theorem originalQComparisonHomotopyEquiv_toFun :
    (originalQComparisonHomotopyEquiv R).toFun = originalQComparison R := rfl

namespace StableCompletion

/-- The original plus-certified completion model is actually equivalent to the original Q unit
component, using precisely its original standard zero-component comparison. -/
def zeroCompletionToOriginalQLoopsHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ZeroComponent R) (OriginalQLoopsZeroComponent R) :=
  pathComponentHomotopyEquiv
    (completionToOriginalQLoopsHomotopyEquiv Rᵐᵒᵖ (stageObject R 0)) (zeroPoint R)
    (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))
    ⟨completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0)⟩

/-- Component restriction preserves the exact accepted standard forward map. -/
theorem zeroCompletionToOriginalQLoopsHomotopyEquiv_toFun :
    (zeroCompletionToOriginalQLoopsHomotopyEquiv R).toFun =
      zeroCompletionToOriginalQLoops R := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rfl

/-- The prescribed original basepoint track still has the upgraded map as its source. -/
def zeroCompletionHomotopyEquivBasepointPath :
    Path (zeroCompletionToOriginalQLoopsHomotopyEquiv R (zeroBase R))
      ⟨Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero),
        mem_pathComponent_self _⟩ :=
  (zeroCompletionToOriginalQLoopsBasepointPath R).cast
    (ContinuousMap.congr_fun (zeroCompletionToOriginalQLoopsHomotopyEquiv_toFun R)
      (zeroBase R)) rfl

/-- The upgraded comparison retains every point of the already-specified basepoint path. -/
theorem zeroCompletionHomotopyEquivBasepointPath_val (t : unitInterval) :
    (zeroCompletionHomotopyEquivBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0) t := rfl

end StableCompletion
end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0602",
  colib_ref "quillen" "KTheory/Plus/ProjectiveCompletionLoopHomotopyEquiv.lean"
    "adaptation" "The original forward maps, inverse homotopies and basepoint tracks are retained"]
  ModuleCat.FiniteProjective.completionToOriginalQLoopsHomotopyEquiv
  ModuleCat.FiniteProjective.originalQComparisonHomotopyEquiv
  ModuleCat.FiniteProjective.StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv
  ModuleCat.FiniteProjective.StableCompletion.zeroCompletionHomotopyEquivBasepointPath_val
