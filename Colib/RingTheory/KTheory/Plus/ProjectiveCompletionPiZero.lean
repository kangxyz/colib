/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionGrothendieck
public import Colib.Topology.ClassifyingSpace.ZerothHomotopy

/-!
# The actual projective-completion path components compute K₀

The native path-component quotient of the nerve realization is identified with
the preexisting exact-category Grothendieck group. The actual vertex of `(A, B)`
represents `[B] - [A]`, and projective object generators return to unit-entry vertices.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory
namespace ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]

/-- Actual topological path components of projective completion are the original exact K₀. -/
def completionPiZeroGrothendieckEquiv :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) ≃
      (exactStructure R).GrothendieckGroup :=
  (classifyingSpaceComponentsEquiv (GroupCompletionCategory R)).symm.trans
    (completionComponentsGrothendieckEquiv R).toEquiv

/-- Every object vertex is sent to its unchanged original grading. -/
@[simp] theorem completionPiZeroGrothendieckEquiv_mk (X : GroupCompletionCategory R) :
    completionPiZeroGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint X)) = completionGrade R X := by
  change completionComponentsGrothendieckEquiv R
    ((classifyingSpaceComponentsEquiv (GroupCompletionCategory R)).symm _) = _
  rw [classifyingSpaceComponentsEquiv_symm_mk]
  rfl

/-- The original pair vertex retains the numerator-minus-denominator convention. -/
@[simp] theorem completionPiZeroGrothendieckEquiv_pair (A B : IsoCategory R) :
    completionPiZeroGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R A B))) =
        coreClass R B - coreClass R A := by
  change completionComponentsGrothendieckEquiv R
    ((classifyingSpaceComponentsEquiv (GroupCompletionCategory R)).symm _) = _
  rw [classifyingSpaceComponentsEquiv_symm_mk]
  rfl

/-- The inverse retains the actual unit-entry vertex of every original projective object. -/
@[simp] theorem completionPiZeroGrothendieckEquiv_symm_class (P : Category.{u, u} R) :
    (completionPiZeroGrothendieckEquiv R).symm
      ((exactStructure R).grothendieckClass P) =
        ZerothHomotopy.mk (classifyingSpacePoint ((completionUnit R).obj ⟨P⟩)) := by
  apply (completionPiZeroGrothendieckEquiv R).injective
  rw [Equiv.apply_symm_apply, completionPiZeroGrothendieckEquiv_mk,
    completionGrade_unit_obj]
  rfl

/-- Two original pair vertices are joined exactly when their original virtual classes agree. -/
theorem completion_joined_iff_grade_eq (X Y : GroupCompletionCategory R) :
    Joined (classifyingSpacePoint X) (classifyingSpacePoint Y) ↔
      completionGrade R X = completionGrade R Y := by
  constructor
  · intro h
    have h' : ZerothHomotopy.mk (classifyingSpacePoint X) =
        ZerothHomotopy.mk (classifyingSpacePoint Y) := Quotient.sound h
    have hh := congrArg (completionPiZeroGrothendieckEquiv R) h'
    simpa only [completionPiZeroGrothendieckEquiv_mk] using hh
  · intro h
    have h' : ZerothHomotopy.mk (classifyingSpacePoint X) =
        ZerothHomotopy.mk (classifyingSpacePoint Y) :=
      (completionPiZeroGrothendieckEquiv R).injective (by
        simpa only [completionPiZeroGrothendieckEquiv_mk] using h)
    exact Quotient.exact h'

end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0378",
  colib_ref "WeibelKBook" "IV, Lemma 3.3 and Lemma 4.3.1" "adaptation"
    "Native path components of the actual nerve realization; pair vertex has value $[B]-[A]$",
  colib_ref "WeibelKBook" "II, Examples 7.1.1-7.1.2" "comparison"
    "The target is the original exact-category Grothendieck group of finite projective modules"]
  ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv
  ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_pair
  ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_symm_class
  ModuleCat.FiniteProjective.completion_joined_iff_grade_eq
