/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EnoughProjectives
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Detecting natural isomorphisms on transfer representables

Use the actual section-indexed coproduct and its kernel presentation. Both steps
are applications of Mathlib's colimit criterion; no projective-retract argument
or exactness assumption is substituted for the presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
  {D : Type v} [Category.{w} D]
  {L L' : PresheafWithTransfers.{u + 1} k ⥤ D}
  [PreservesColimitsOfSize.{u + 1, u + 1} L]
  [PreservesColimitsOfSize.{u + 1, u + 1} L']

/-- A natural transformation between colimit-preserving functors on transfer
presheaves is invertible if it is invertible on the actual transfer representables. -/
theorem isIso_app_of_isIso_representable (α : L ⟶ L')
    (hα : ∀ X : Cor k, IsIso (α.app ((representableLarge k).obj X)))
    (P : PresheafWithTransfers.{u + 1} k) : IsIso (α.app P) := by
  have hcover (Q : PresheafWithTransfers.{u + 1} k) :
      IsIso (α.app (representableCover Q)) := by
    let K := Discrete.functor (representableCoverFamily Q)
    have : ∀ i, IsIso ((Functor.whiskerLeft K α).app i) := fun i => hα i.as.1
    have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K α _ (colimit.isColimit K)
  let K := parallelPair (representablePresentationRelation P) 0
  have : ∀ i, IsIso ((Functor.whiskerLeft K α).app i) := by
    intro i
    cases i <;> exact hcover _
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _ (representablePresentationIsColimit P)

end AlgebraicGeometry.PresheafWithTransfers
