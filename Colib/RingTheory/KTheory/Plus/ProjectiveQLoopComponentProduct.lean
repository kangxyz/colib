/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckComparison.LoopComponentProduct
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionLoopLabels

/-!
# The original finite-projective Q-loop product has the standard positive labels

This specializes the actual normalized product to the original Q category
and checks its first coordinate on the accepted standard comparison and on
all right-module completion stages. The neutral factor is the actual constant
loop component. Identifying that factor with the original BGL-plus space is
not asserted and still requires the remaining comparison upgrade.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveQLoopComponentProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]

/-- The literal original Q-loop product with its unchanged neutral path component. -/
def originalQLoopProductEquiv := (exactStructure.{u, u} R).qLoopProductEquiv

/-- The first coordinate of the exact standard comparison is its positive algebraic K₀ label. -/
theorem originalQLoopProductEquiv_comparison_label
    (x : ClassifyingSpace (GroupCompletionCategory R)) :
    ((originalQLoopProductEquiv R (originalQComparison R x)).1).ofTopology =
      completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) := by
  rw [originalQLoopProductEquiv,
    CategoryTheory.ExactCategory.ExactStructure.qLoopProductEquiv_label]
  exact originalQComparison_kZero R x

/-- A standard right-module completion stage has numerator-minus-denominator product coordinate. -/
theorem originalQLoopProductEquiv_stage_label (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    ((originalQLoopProductEquiv Rᵐᵒᵖ
      (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))).1).ofTopology =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [originalQLoopProductEquiv,
    CategoryTheory.ExactCategory.ExactStructure.qLoopProductEquiv_label]
  exact completionToOriginalQLoops_stage_kZero R n P

/-- The original constant-loop component is included exactly on the neutral product slice. -/
theorem originalQLoopProductEquiv_neutral_slice
    (z : (exactStructure.{u, u} R).QLoopIdentityComponent) :
    (originalQLoopProductEquiv R).invFun
      ((exactStructure R).discreteKZeroIdentity, z) = z.val :=
  (exactStructure R).qLoopComponentProductEquiv_identity z

end ModuleCat.FiniteProjective
