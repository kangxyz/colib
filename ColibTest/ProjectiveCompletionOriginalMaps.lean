/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionPiZeroNaturality
import Colib.Topology.ClassifyingSpace.ProjectiveCompletionBaseChange

/-! The degree-zero comparison uses the original completion category and ring-change map. -/

noncomputable section
universe u
open CategoryTheory ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

example : GroupCompletionCategory Rᵐᵒᵖ = StableCompletion.Completion R := rfl

example : completionBaseChange f = GroupCompletion.monoidalMap (rightBaseChange f).core := rfl

example (x : CategoryTheory.ConnectedComponents (StableCompletion.Completion R)) :
    completionComponentsGrothendieckEquiv Sᵐᵒᵖ
      ((completionBaseChange f).mapConnectedComponents x) =
        (rightBaseChangeExact f).grothendieckMap
          (completionComponentsGrothendieckEquiv Rᵐᵒᵖ x) :=
  completionComponentsGrothendieckEquiv_baseChange f x

example (A B : IsoCategory Rᵐᵒᵖ) :
    completionPiZeroGrothendieckEquiv Sᵐᵒᵖ
      (ZerothHomotopy.mk (completionBaseChangeMap f
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ A B)))) =
        (rightBaseChangeExact f).grothendieckMap (coreClass Rᵐᵒᵖ B - coreClass Rᵐᵒᵖ A) := by
  have hv : completionBaseChangeMap f
      (classifyingSpacePoint (completionPair Rᵐᵒᵖ A B)) =
        classifyingSpacePoint ((completionBaseChange f).obj (completionPair Rᵐᵒᵖ A B)) :=
    classifyingSpaceMapUniversal_point _ _
  exact (congrArg (fun y : ClassifyingSpace (GroupCompletionCategory Sᵐᵒᵖ) ↦
    completionPiZeroGrothendieckEquiv Sᵐᵒᵖ (ZerothHomotopy.mk y)) hv).trans
      ((completionPiZeroGrothendieckEquiv_mk Sᵐᵒᵖ
        ((completionBaseChange f).obj (completionPair Rᵐᵒᵖ A B))).trans
          (completionComponentsGrothendieckEquiv_baseChange f
            (CategoryTheory.ConnectedComponents.mk (completionPair Rᵐᵒᵖ A B))))

example (x : ZerothHomotopy (ClassifyingSpace (StableCompletion.Completion R))) :
    completionPiZeroGrothendieckEquiv Sᵐᵒᵖ
      (Quotient.map (sa := pathSetoid (ClassifyingSpace (StableCompletion.Completion R)))
        (sb := pathSetoid (ClassifyingSpace (StableCompletion.Completion S)))
        (completionBaseChangeMap f)
        (fun _ _ h ↦ h.map (completionBaseChangeMap f).continuous) x) =
      (rightBaseChangeExact f).grothendieckMap
        (completionPiZeroGrothendieckEquiv Rᵐᵒᵖ x) := by
  have hq : Quotient.map
      (sa := pathSetoid (ClassifyingSpace (StableCompletion.Completion R)))
      (sb := pathSetoid (ClassifyingSpace (StableCompletion.Completion S)))
      (completionBaseChangeMap f)
      (fun _ _ h ↦ h.map (completionBaseChangeMap f).continuous) x =
        Quotient.map
          (sa := pathSetoid (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)))
          (sb := pathSetoid (ClassifyingSpace (GroupCompletionCategory Sᵐᵒᵖ)))
          (classifyingSpaceMap
            (C := GroupCompletionCategory Rᵐᵒᵖ) (D := GroupCompletionCategory Sᵐᵒᵖ)
            (GroupCompletion.monoidalMap (rightBaseChange f).core))
          (fun _ _ h ↦ h.map (classifyingSpaceMap
            (C := GroupCompletionCategory Rᵐᵒᵖ) (D := GroupCompletionCategory Sᵐᵒᵖ)
            (GroupCompletion.monoidalMap (rightBaseChange f).core)).hom.continuous) x := by
    induction x using ZerothHomotopy.rec with
    | mk y =>
      apply congrArg ZerothHomotopy.mk
      exact DFunLike.congr_fun (classifyingSpaceMapUniversal_eq (completionBaseChange f)) y
  exact (congrArg (completionPiZeroGrothendieckEquiv Sᵐᵒᵖ) hq).trans
    (completionPiZeroGrothendieckEquiv_baseChange f x)

example : completionPiZeroGrothendieckEquiv Rᵐᵒᵖ
    (ZerothHomotopy.mk (StableCompletion.zeroPoint R)) = 0 := by
  exact (completionPiZeroGrothendieckEquiv_pair Rᵐᵒᵖ
    (rankOnePower Rᵐᵒᵖ 0) (rankOnePower Rᵐᵒᵖ 0)).trans (sub_self _)

example : ZerothHomotopy.mk (completionBaseChangeMap f (StableCompletion.zeroPoint R)) =
    ZerothHomotopy.mk (StableCompletion.zeroPoint S) :=
  ZerothHomotopy.sound (completionBaseChangeBasepointPath f)
