/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveGroupCompletion
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionBaseChange
public import Colib.KTheory.GrothendieckComparison.Naturality

/-!
# Naturality of the original completion's virtual object classes

The actual completion change-of-rings functor preserves numerator-minus-
denominator grading through the original exact-functor Grothendieck map.
Applying the existing algebraic-to-homotopical comparison gives naturality
of these virtual object classes in the original Quillen K₀.

These are object-class statements. No identification of path components with
K₀, and no product decomposition of a completion space, is asserted.
-/

open CategoryTheory Topology

@[expose] public section

noncomputable section

universe u

namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

/-- The actual virtual grade, mapped to the preexisting homotopical Quillen K₀. -/
def completionKZeroClass (R : Type u) [Ring R] (X : GroupCompletionCategory R) :
    (exactStructure R).K 0 :=
  (exactStructure R).grothendieckToKZero (Multiplicative.ofAdd (completionGrade R X))

/-- The virtual class has exactly the original numerator and denominator object classes. -/
theorem completionKZeroClass_eq_objectClasses (R : Type u) [Ring R]
    (X : GroupCompletionCategory R) :
    completionKZeroClass R X =
      (exactStructure R).kZeroObjectClass X.obj.2.of /
        (exactStructure R).kZeroObjectClass X.obj.1.of := by
  simp only [completionKZeroClass, completionGrade, coreClass, ofAdd_sub,
    map_div, CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_class]

variable {R S : Type u} [Ring R] [Ring S]

/-- Actual change of rings preserves the original numerator-minus-denominator grade. -/
theorem completionGrade_baseChange (f : R →+* S) (X : StableCompletion.Completion R) :
    completionGrade Sᵐᵒᵖ ((completionBaseChange f).obj X) =
      (rightBaseChangeExact f).grothendieckMap (completionGrade Rᵐᵒᵖ X) := by
  change
    (exactStructure Sᵐᵒᵖ).grothendieckClass ((rightBaseChange f).obj X.obj.2.of) -
        (exactStructure Sᵐᵒᵖ).grothendieckClass ((rightBaseChange f).obj X.obj.1.of) =
      (rightBaseChangeExact f).grothendieckMap
        ((exactStructure Rᵐᵒᵖ).grothendieckClass X.obj.2.of -
          (exactStructure Rᵐᵒᵖ).grothendieckClass X.obj.1.of)
  rw [map_sub, CategoryTheory.ExactCategory.ExactFunctor.grothendieckMap_class,
    CategoryTheory.ExactCategory.ExactFunctor.grothendieckMap_class]
  rfl

/-- The original K₀ map sends each virtual completion object class to that of its
actual change-of-rings image. -/
theorem completionKZeroClass_baseChange (f : R →+* S)
    (X : StableCompletion.Completion R) :
    (rightBaseChangeExact f).KMap 0 (completionKZeroClass Rᵐᵒᵖ X) =
      completionKZeroClass Sᵐᵒᵖ ((completionBaseChange f).obj X) := by
  have h := DFunLike.congr_fun (rightBaseChangeExact f).grothendieckToKZero_naturality
    (Multiplicative.ofAdd (completionGrade Rᵐᵒᵖ X))
  change (rightBaseChangeExact f).KMap 0 (completionKZeroClass Rᵐᵒᵖ X) =
    (exactStructure Sᵐᵒᵖ).grothendieckToKZero
      (Multiplicative.ofAdd
        ((rightBaseChangeExact f).grothendieckMap (completionGrade Rᵐᵒᵖ X))) at h
  rw [← completionGrade_baseChange f X] at h
  exact h

end ModuleCat.FiniteProjective
