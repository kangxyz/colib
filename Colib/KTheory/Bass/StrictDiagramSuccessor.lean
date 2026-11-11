/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagram

/-!
# Exact iteration identities for the original strict Bass endofunctor

The existing recursive iterate composes the Bass functor on the left. Associativity also
identifies its successor with composition on the right, as an equality of the actual functors.
This retains their full action on original natural transformations and coefficient maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- The original successor iterate is also the original iterate followed by Bass. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramIteration.lean:25"
  "adaptation" "Original equality of the entire successor Bass functor"]
theorem strictDiagramIterate_succ_right (n : ℕ) :
    strictDiagramIterate.{u, v, w} Q (n + 1) =
      strictDiagramIterate Q n ⋙ strictDiagramFunctor Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change strictDiagramFunctor Q ⋙ strictDiagramIterate Q (n + 1) =
      (strictDiagramFunctor Q ⋙ strictDiagramIterate Q n) ⋙ strictDiagramFunctor Q
    rw [ih]
    rfl

end KTheory.Bass
