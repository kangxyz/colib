/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentWeakEquivalence

/-! # The standard zero-completion comparison into the original Q loop component -/
open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionZeroLoops.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
universe u
namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The identity component in the unchanged original loop space of Q. -/
abbrev OriginalQLoopsZeroComponent :=
  pathComponent (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))

/-- The standard completion-to-loop map restricted to its actual zero component. -/
def zeroCompletionToOriginalQLoops : C(ZeroComponent R, OriginalQLoopsZeroComponent R) :=
  pathComponentMap (completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0))
    (zeroPoint R) (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))
    ⟨completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0)⟩

/-- The underlying map is precisely the parameterized standard comparison into original Q. -/
@[simp] theorem zeroCompletionToOriginalQLoops_val (x : ZeroComponent R) :
    (zeroCompletionToOriginalQLoops R x).val =
      completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0) x.val := rfl

/-- The actual component comparison is a weak equivalence, including degree zero. -/
theorem zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (zeroCompletionToOriginalQLoops R) :=
  (completionToOriginalQLoops_isWeakHomotopyEquivalence Rᵐᵒᵖ (stageObject R 0)).pathComponentMap
    (zeroPoint R) _ ⟨completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0)⟩

/-- The basepoint track is the restriction of the specified standard comparison track. -/
def zeroCompletionToOriginalQLoopsBasepointPath :
    Path (zeroCompletionToOriginalQLoops R (zeroBase R))
      ⟨Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero),
        mem_pathComponent_self _⟩ :=
  pathComponentMapBasepointPath _ (zeroPoint R) _
    (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0))

/-- Restriction retains every point of the specified standard track without reparametrization. -/
@[simp] theorem zeroCompletionToOriginalQLoopsBasepointPath_val (t : unitInterval) :
    (zeroCompletionToOriginalQLoopsBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0) t := rfl

end ModuleCat.FiniteProjective.StableCompletion
