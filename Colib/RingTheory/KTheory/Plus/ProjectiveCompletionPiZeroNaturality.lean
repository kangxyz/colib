/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionPiZero
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeMonoidal
public import Colib.CategoryTheory.GroupCompletion.ConnectedComponentsMap
public import Colib.KTheory.GrothendieckGroup.Map

/-!
# Change of rings for the actual projective-completion K₀ comparison

The original right-module scalar-extension functor acts on both coordinates and
the common denominator. Its actual nerve-realization map agrees on path
components with the original exact-functor map on Grothendieck groups.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory MonoidalCategory
namespace ModuleCat.FiniteProjective

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The original change-of-rings completion functor has the original exact K₀ map on components. -/
theorem completionComponentsGrothendieckEquiv_baseChange
    (x : ConnectedComponents (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionComponentsGrothendieckEquiv Sᵐᵒᵖ
      ((GroupCompletion.monoidalMap (rightBaseChange f).core).mapConnectedComponents x) =
        (rightBaseChangeExact f).grothendieckMap
          (completionComponentsGrothendieckEquiv Rᵐᵒᵖ x) := by
  induction x using Quotient.inductionOn with
  | h X =>
    change coreClass Sᵐᵒᵖ ((rightBaseChange f).core.obj X.obj.2) -
      coreClass Sᵐᵒᵖ ((rightBaseChange f).core.obj X.obj.1) =
        (rightBaseChangeExact f).grothendieckMap
          (coreClass Rᵐᵒᵖ X.obj.2 - coreClass Rᵐᵒᵖ X.obj.1)
    rw [map_sub]
    exact (congrArg₂ (fun a b => a - b)
      ((rightBaseChangeExact f).grothendieckMap_class X.obj.2.of).symm
      ((rightBaseChangeExact f).grothendieckMap_class X.obj.1.of).symm)

/-- The additive naturality square uses the native two-coordinate component homomorphism. -/
theorem completionComponentsGrothendieckEquiv_baseChange_hom :
    (completionComponentsGrothendieckEquiv Sᵐᵒᵖ).toAddMonoidHom.comp
      (GroupCompletion.monoidalMapComponents (rightBaseChange f).core) =
        (rightBaseChangeExact f).grothendieckMap.comp
          (completionComponentsGrothendieckEquiv Rᵐᵒᵖ).toAddMonoidHom := by
  ext x
  exact completionComponentsGrothendieckEquiv_baseChange f x

/-- The path-component comparison commutes with the actual continuous change-of-rings map. -/
theorem completionPiZeroGrothendieckEquiv_baseChange
    (x : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    completionPiZeroGrothendieckEquiv Sᵐᵒᵖ
      (Quotient.map
        (sa := pathSetoid (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)))
        (sb := pathSetoid (ClassifyingSpace (GroupCompletionCategory Sᵐᵒᵖ)))
        (classifyingSpaceMap (C := GroupCompletionCategory Rᵐᵒᵖ)
          (D := GroupCompletionCategory Sᵐᵒᵖ)
          (GroupCompletion.monoidalMap (rightBaseChange f).core))
        (fun {_ _} h ↦
          h.map (classifyingSpaceMap (C := GroupCompletionCategory Rᵐᵒᵖ)
            (D := GroupCompletionCategory Sᵐᵒᵖ)
            (GroupCompletion.monoidalMap (rightBaseChange f).core)).hom.continuous) x) =
        (rightBaseChangeExact f).grothendieckMap
          (completionPiZeroGrothendieckEquiv Rᵐᵒᵖ x) := by
  obtain ⟨c, rfl⟩ := (classifyingSpaceComponentsEquiv (GroupCompletionCategory Rᵐᵒᵖ)).surjective x
  have h := classifyingSpaceComponentsEquiv_naturality
    (C := GroupCompletionCategory Rᵐᵒᵖ) (D := GroupCompletionCategory Sᵐᵒᵖ)
    (GroupCompletion.monoidalMap (rightBaseChange f).core) c
  have hR : completionPiZeroGrothendieckEquiv Rᵐᵒᵖ
      (classifyingSpaceComponentsEquiv (GroupCompletionCategory Rᵐᵒᵖ) c) =
        completionComponentsGrothendieckEquiv Rᵐᵒᵖ c :=
    congrArg (completionComponentsGrothendieckEquiv Rᵐᵒᵖ)
      ((classifyingSpaceComponentsEquiv (GroupCompletionCategory Rᵐᵒᵖ)).symm_apply_apply c)
  have hS : completionPiZeroGrothendieckEquiv Sᵐᵒᵖ
      (classifyingSpaceComponentsEquiv (GroupCompletionCategory Sᵐᵒᵖ)
        ((GroupCompletion.monoidalMap (rightBaseChange f).core).mapConnectedComponents c)) =
      completionComponentsGrothendieckEquiv Sᵐᵒᵖ
        ((GroupCompletion.monoidalMap (rightBaseChange f).core).mapConnectedComponents c) :=
    congrArg (completionComponentsGrothendieckEquiv Sᵐᵒᵖ)
      ((classifyingSpaceComponentsEquiv (GroupCompletionCategory Sᵐᵒᵖ)).symm_apply_apply _)
  exact (congrArg (completionPiZeroGrothendieckEquiv Sᵐᵒᵖ) h.symm).trans
    (hS.trans ((completionComponentsGrothendieckEquiv_baseChange f c).trans
      (congrArg (rightBaseChangeExact f).grothendieckMap hR.symm)))

end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0378",
  colib_ref "WeibelKBook" "IV, Definition 4.2 and Lemma 4.3.1" "comparison"
    "The actual strong monoidal right-module base change agrees with its original exact K-zero map"]
  ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange
  ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange_hom
  ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_baseChange
