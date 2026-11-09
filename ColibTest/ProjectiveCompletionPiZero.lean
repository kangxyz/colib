/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionPiZeroNaturality

/-! Regression consumers for the actual projective-completion equivalences and signs. -/

noncomputable section
universe u
open CategoryTheory ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]

example : AddCommGroup (CategoryTheory.ConnectedComponents (GroupCompletionCategory R)) :=
  inferInstance

example : CategoryTheory.ConnectedComponents (GroupCompletionCategory R) ≃+
    (exactStructure R).GrothendieckGroup := completionComponentsGrothendieckEquiv R

example : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) ≃
    (exactStructure R).GrothendieckGroup := completionPiZeroGrothendieckEquiv R

example (A B : IsoCategory R) :
    completionComponentsGrothendieckEquiv R
      (CategoryTheory.ConnectedComponents.mk (completionPair R A B)) =
        coreClass R B - coreClass R A := rfl

example (A B : IsoCategory R) :
    completionPiZeroGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R A B))) =
        coreClass R B - coreClass R A := completionPiZeroGrothendieckEquiv_pair R A B

example (P : ModuleCat.FiniteProjective.Category.{u, u} R) :
    (completionPiZeroGrothendieckEquiv R).symm
      ((exactStructure R).grothendieckClass P) =
        ZerothHomotopy.mk (classifyingSpacePoint ((completionUnit R).obj ⟨P⟩)) :=
  completionPiZeroGrothendieckEquiv_symm_class R P

example (x : CategoryTheory.ConnectedComponents (GroupCompletionCategory R)) :
    grothendieckToCompletionComponents R (completionComponentGrade R x) = x :=
  (completionComponentsGrothendieckEquiv R).symm_apply_apply x

example (x : (exactStructure R).GrothendieckGroup) :
    completionComponentGrade R (grothendieckToCompletionComponents R x) = x :=
  (completionComponentsGrothendieckEquiv R).apply_symm_apply x

example (X Y : GroupCompletionCategory R) :
    completionGrade R X = completionGrade R Y ↔ Zigzag X Y :=
  completionGrade_eq_iff_zigzag R X Y

example (X Y : GroupCompletionCategory R) :
    Joined (classifyingSpacePoint X) (classifyingSpacePoint Y) ↔
      completionGrade R X = completionGrade R Y := completion_joined_iff_grade_eq R X Y

example (x y : CategoryTheory.ConnectedComponents (GroupCompletionCategory R)) :
    completionComponentsGrothendieckEquiv R (x + y) =
      completionComponentsGrothendieckEquiv R x + completionComponentsGrothendieckEquiv R y :=
  map_add _ _ _

example (x : CategoryTheory.ConnectedComponents (GroupCompletionCategory R)) :
    completionComponentsGrothendieckEquiv R (-x) =
      -completionComponentsGrothendieckEquiv R x := map_neg _ _

example (P : IsoCategory R) :
    completionPiZeroGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R P P))) = 0 := by
  rw [completionPiZeroGrothendieckEquiv_pair, sub_self]

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  rightBaseChangeCoreMonoidal

variable {R} {S : Type u} [Ring S] (f : R →+* S)

example (x : CategoryTheory.ConnectedComponents (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionComponentsGrothendieckEquiv Sᵐᵒᵖ
      ((GroupCompletion.monoidalMap (rightBaseChange f).core).mapConnectedComponents x) =
        (rightBaseChangeExact f).grothendieckMap
          (completionComponentsGrothendieckEquiv Rᵐᵒᵖ x) :=
  completionComponentsGrothendieckEquiv_baseChange f x

example (A B : IsoCategory Rᵐᵒᵖ) :
    completionPiZeroGrothendieckEquiv Sᵐᵒᵖ
      (ZerothHomotopy.mk (classifyingSpaceMap
        (GroupCompletion.monoidalMap (rightBaseChange f).core)
          (classifyingSpacePoint (completionPair Rᵐᵒᵖ A B)))) =
        (rightBaseChangeExact f).grothendieckMap (coreClass Rᵐᵒᵖ B - coreClass Rᵐᵒᵖ A) := by
  exact (completionPiZeroGrothendieckEquiv_baseChange f
    (ZerothHomotopy.mk (classifyingSpacePoint (completionPair Rᵐᵒᵖ A B)))).trans
      (congrArg (rightBaseChangeExact f).grothendieckMap
        (completionPiZeroGrothendieckEquiv_pair Rᵐᵒᵖ A B))
