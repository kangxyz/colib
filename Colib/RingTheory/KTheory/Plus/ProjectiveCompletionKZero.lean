/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionGrothendieck
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionGradeNaturality
public import Colib.KTheory.GrothendieckComparison.Injectivity

/-! # Homotopical K-zero of projective completion components

The homotopical clauses of `Quillen/KTheory/Plus/ProjectiveCompletionKZero.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` use the existing native Grothendieck equivalence.
No second component model is introduced.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The actual categorical components identify with homotopical Quillen K-zero. -/
def completionComponentKZeroEquiv :
    ConnectedComponents (GroupCompletionCategory R) ≃ (exactStructure R).K 0 :=
  (completionComponentsGrothendieckEquiv R).toEquiv.trans
    (Multiplicative.ofAdd.trans (exactStructure R).grothendieckKZeroEquiv.toEquiv)

@[simp] theorem completionComponentKZeroEquiv_mk (X : GroupCompletionCategory R) :
    completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk X) =
      completionKZeroClass R X := rfl

/-- The unchanged object classes are numerator divided by denominator. -/
theorem completionComponentKZeroEquiv_pair (A B : IsoCategory R) :
    completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk (completionPair R A B)) =
      (exactStructure R).kZeroObjectClass B.of / (exactStructure R).kZeroObjectClass A.of :=
  completionKZeroClass_eq_objectClasses R (completionPair R A B)
end ModuleCat.FiniteProjective
