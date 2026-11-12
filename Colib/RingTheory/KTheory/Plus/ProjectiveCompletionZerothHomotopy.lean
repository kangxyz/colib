/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionKZero
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionPiZeroNaturality

/-! # Actual completion path components and homotopical K-zero

The original homotopical clauses of `Quillen/KTheory/Plus/ProjectiveCompletionZerothHomotopy.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` extend the native path-component grading.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable (R : Type u) [Ring R]

/-- The unchanged path-component grading followed by the original Quillen K-zero map. -/
def completionZerothHomotopyKZeroEquiv :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) ≃ (exactStructure R).K 0 :=
  (completionPiZeroGrothendieckEquiv R).trans
    (Multiplicative.ofAdd.trans (exactStructure R).grothendieckKZeroEquiv.toEquiv)

@[simp] theorem completionZerothHomotopyKZeroEquiv_point (X : GroupCompletionCategory R) :
    completionZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint X)) = completionKZeroClass R X := by
  change (exactStructure R).grothendieckKZeroEquiv
    (Multiplicative.ofAdd (completionPiZeroGrothendieckEquiv R _)) = _
  rw [completionPiZeroGrothendieckEquiv_mk]
  rfl

/-- The two original object classes retain the numerator-minus-denominator convention. -/
theorem completionZerothHomotopyKZeroEquiv_pair (A B : IsoCategory R) :
    completionZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R A B))) =
      (exactStructure R).kZeroObjectClass B.of / (exactStructure R).kZeroObjectClass A.of := by
  rw [completionZerothHomotopyKZeroEquiv_point]
  exact completionKZeroClass_eq_objectClasses R _

variable {R} {S : Type u} [Ring S]

/-- The actual completion ring-change map on its unchanged path components. -/
def completionZerothHomotopyBaseChange (f : R →+* S) :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) →
      ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Sᵐᵒᵖ)) :=
  ZerothHomotopy.lift (fun x ↦ ZerothHomotopy.mk (completionBaseChangeMap f x))
    (fun _ _ p ↦ ZerothHomotopy.sound (p.map (completionBaseChangeMap f).continuous))

@[simp] theorem completionZerothHomotopyBaseChange_mk (f : R →+* S)
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionZerothHomotopyBaseChange f (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (completionBaseChangeMap f x) := rfl

/-- The path-component ring-change map retains the actual image vertex. -/
theorem completionZerothHomotopyBaseChange_point (f : R →+* S)
    (X : GroupCompletionCategory Rᵐᵒᵖ) :
    completionZerothHomotopyBaseChange f (ZerothHomotopy.mk (classifyingSpacePoint X)) =
      ZerothHomotopy.mk (classifyingSpacePoint ((completionBaseChange f).obj X)) := by
  rw [completionZerothHomotopyBaseChange_mk]
  exact congrArg ZerothHomotopy.mk (classifyingSpaceMapUniversal_point (completionBaseChange f) X)

/-- Naturality keeps the original homotopical K-zero and completion ring-change maps. -/
theorem completionZerothHomotopyKZeroEquiv_baseChange (f : R →+* S)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    (rightBaseChangeExact f).KMap 0 (completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ a) =
      completionZerothHomotopyKZeroEquiv Sᵐᵒᵖ (completionZerothHomotopyBaseChange f a) := by
  obtain ⟨c, hc⟩ := (classifyingSpaceComponentsEquiv (GroupCompletionCategory Rᵐᵒᵖ)).surjective a
  induction c using Quotient.inductionOn with
  | h X =>
    subst a
    rw [classifyingSpaceComponentsEquiv_mk, completionZerothHomotopyBaseChange_point,
      completionZerothHomotopyKZeroEquiv_point]
    change _ = completionZerothHomotopyKZeroEquiv Sᵐᵒᵖ
      (ZerothHomotopy.mk (classifyingSpacePoint
        ((GroupCompletion.monoidalMap (rightBaseChange f).core).obj X)))
    rw [completionZerothHomotopyKZeroEquiv_point]
    exact completionKZeroClass_baseChange f X
end ModuleCat.FiniteProjective
