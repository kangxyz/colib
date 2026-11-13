/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionFiberNaturality
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Colib.Topology.HomotopyFiber.LoopComparisonHomotopy

/-!
# Space-level naturality of the original projective-completion loop comparison

The standard completion-to-original-Q-loop maps commute with actual ring base
change up to an actual continuous homotopy. Pointwise loop reversal maps the
generic loop/fiber homotopy, retaining the normalized Q map and monoidal unit path.
Only the genuine loop/fiber homotopy equivalences are cancelled;
no Whitehead upgrade or inference from equality on homotopy groups is used.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionLoopNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology

universe u

namespace ModuleCat.FiniteProjective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The standard ordinary naturality homotopy reverses the inner loop coordinate
of the generic loop/fiber homotopy. Specified comparison paths remain separate based data. -/
def completionToOriginalQLoopsBaseChangeHomotopy :
    ((basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (completionNormalizedQ_basepoint f)).comp
        (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0))).Homotopy
    ((completionToOriginalQLoops Sᵐᵒᵖ (StableCompletion.stageObject S 0)).comp
      (completionBaseChangeMap f)) := by
  let := localizedExtension_classifyingSpace_contractible Rᵐᵒᵖ
  let := localizedExtension_classifyingSpace_contractible Sᵐᵒᵖ
  let H := HomotopyFiber.loopComparisonNaturalityHomotopy
    (classifyingSpaceMapUniversal (localizedExtensionBaseChange f))
    (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
    (completionNormalizedProjectionHomotopy f)
    (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
    (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
    (completionNormalizedQ_basepoint f)
    (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)
    (completionToOriginalQHomotopyFiber Sᵐᵒᵖ) (completionBaseChangeMap f)
    (completionFiberNaturality f) (StableCompletion.zeroPoint R)
    (StableCompletion.zeroPoint S) (completionBaseChangeBasepointPath f)
  exact
    { toFun := fun z ↦ loopReversal (H z)
      continuous_toFun := loopReversal.continuous.comp H.continuous
      map_zero_left := fun x ↦
        (congrArg loopReversal (H.apply_zero x)).trans
          (basedLoopMap_loopReversal
            (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
            (completionNormalizedQ_basepoint f) _).symm
      map_one_left := fun x ↦ congrArg loopReversal (H.apply_one x) }

end ModuleCat.FiniteProjective
