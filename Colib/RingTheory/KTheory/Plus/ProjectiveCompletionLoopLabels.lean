/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionLoopKZero
public import Colib.RingTheory.KTheory.Plus.ProjectiveTelescopeKZero

/-!
# Original Q-loop labels of completion stages and change of rings

With the unchanged canonical zero-stage basepoint, the standard Q-loop label
is the existing completion K₀ label. A stage with numerator `P` and denominator
`rankOnePower n` therefore has class `[P] - [rankOnePower n]`. Arbitrary unital
change of rings commutes with these labels. No invariant-basis-number assumption is used.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionLoopLabels.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
variable (R : Type u) [Ring R]

/-- The canonical standard zero-stage comparison preserves the algebraic grade. -/
theorem completionToOriginalQLoopsComponents_zeroStage
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (completionToOriginalQLoopsComponents Rᵐᵒᵖ (StableCompletion.stageObject R 0) a) =
        completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ a :=
  completionToOriginalQLoopsComponents_kZero_of_grade_zero Rᵐᵒᵖ
    (StableCompletion.stageObject R 0) (completionGrade_diagonal Rᵐᵒᵖ _) a

/-- The actual loop label of every original stage is numerator class divided by denominator
class. -/
theorem completionToOriginalQLoops_stage_kZero (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))) =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [← completionToOriginalQLoopsComponents_mk,
    completionToOriginalQLoopsComponents_zeroStage, completionZerothHomotopyKZeroEquiv_pair]

/-- The original telescope and its original completion map have the same exact Q-loop stage
label. -/
theorem telescopeToOriginalQLoops_stage_kZero (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    (exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpaceMapUniversal (StableFreeRight.completionFunctor R)
          (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))))) =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [classifyingSpaceMapUniversal_point, StableFreeRight.completionFunctor_obj]
  exact completionToOriginalQLoops_stage_kZero R n P

variable {R} {S : Type u} [Ring S]

/-- Original ring change commutes with the actual loop-induced K₀ labels, including their sign. -/
theorem completionToOriginalQLoopsComponents_kZero_baseChange (f : R →+* S)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    (rightBaseChangeExact f).KMap 0
      ((exactStructure Rᵐᵒᵖ).loopComponentsKZeroEquiv
        (completionToOriginalQLoopsComponents Rᵐᵒᵖ (StableCompletion.stageObject R 0) a)) =
      (exactStructure Sᵐᵒᵖ).loopComponentsKZeroEquiv
        (completionToOriginalQLoopsComponents Sᵐᵒᵖ (StableCompletion.stageObject S 0)
          (completionZerothHomotopyBaseChange f a)) := by
  rw [completionToOriginalQLoopsComponents_zeroStage,
    completionToOriginalQLoopsComponents_zeroStage,
    completionZerothHomotopyKZeroEquiv_baseChange]

/-- The literal normalized-Q loop square agrees under the unchanged original K₀ identification. -/
theorem completionToOriginalQLoops_normalizedQ_kZero_square (f : R →+* S)
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    (exactStructure Sᵐᵒᵖ).loopComponentsKZeroEquiv
      (ZerothHomotopy.mk
        (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
          (rightBaseChangeExact f).normalizedQ_map_point
          (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0) x))) =
      (exactStructure Sᵐᵒᵖ).loopComponentsKZeroEquiv
        (ZerothHomotopy.mk
          (completionToOriginalQLoops Sᵐᵒᵖ (StableCompletion.stageObject S 0)
            (completionBaseChangeMap f x))) := by
  rw [← CategoryTheory.ExactCategory.ExactFunctor.loopComponentsKZeroEquiv_naturality]
  exact completionToOriginalQLoopsComponents_kZero_baseChange f (ZerothHomotopy.mk x)

end ModuleCat.FiniteProjective
