/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZeroLoopNaturality

/-!
# Independent original plus-certified Q-loop equivalence client

Consume both actual inverse homotopies, the exact standard forward map, and
the existing ordinary base-change homotopy after upgrading the zero-component
comparison. No identification of arbitrary supplied plus models or coherence
of selected inverse maps is asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory Topology ModuleCat.FiniteProjective
open scoped Topology
universe u
namespace Consumer.OriginalQLoopHomotopyEquiv

variable (R : Type u) [Ring R]

/-- The original full standard comparison now has an actual inverse path on its source. -/
def recoverCompletionPoint (x : ClassifyingSpace (GroupCompletionCategory R)) :
    Path ((originalQComparisonHomotopyEquiv R).invFun (originalQComparison R x)) x :=
  (originalQComparisonHomotopyEquiv R).left_inv.some.evalAt x

/-- The same actual inverse gives the displayed right-inverse path on original Q loops. -/
def recoverOriginalLoop
    (γ : Path (classifyingSpacePoint (exactStructure.{u, u} R).qZero)
      (classifyingSpacePoint (exactStructure.{u, u} R).qZero)) :
    Path (originalQComparison R ((originalQComparisonHomotopyEquiv R).invFun γ)) γ :=
  (originalQComparisonHomotopyEquiv R).right_inv.some.evalAt γ

/-- The independently constructed original plus-certified target has an actual component inverse. -/
def recoverOriginalPlusPoint (x : StableCompletion.ZeroComponent R) :
    Path ((StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv R).invFun
      (StableCompletion.zeroCompletionToOriginalQLoops R x)) x :=
  (StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv R).left_inv.some.evalAt x

/-- The component equivalence still has the exact original standard zero map as forward map. -/
theorem original_plus_forward :
    (StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv R).toFun =
      StableCompletion.zeroCompletionToOriginalQLoops R :=
  StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv_toFun R

variable {R} {S : Type u} [Ring S]

/-- Upgrading the exact forward maps retains the existing ordinary ring-change homotopy. -/
def originalPlusBaseChangeHomotopy (f : R →+* S) :
    ((StableCompletion.zeroOriginalQLoopsBaseChangeMap f).comp
      (StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv R).toFun).Homotopy
        ((StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv S).toFun.comp
          (zeroCompletionBaseChangeMap f)) := by
  simpa only [StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv_toFun] using
    StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy f

end Consumer.OriginalQLoopHomotopyEquiv
