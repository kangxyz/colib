/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Functor.IdentityAutomorphism

/-!
# Preservation of identity actions through faithful evaluation

The predicates retain the same original functors and supplied automorphisms while sharing
their categorical types. A literal evaluation square and faithfulness transfer the original
evaluated action formulas to the original functor. No action or comparison is replaced.
-/
/-! Adapted from `Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismEvaluation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v' u'' v''
namespace CategoryTheory.Functor.IdentityAutomorphism

/-- The original functor intertwines every forward component of the two supplied actions. -/
def Preserves {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) : Prop :=
  ∀ S, F.map (α.hom.app S) = β.hom.app (F.obj S)

/-- The original evaluation data transfer any pair of matching evaluated identity actions. -/
def EvaluationPreserves {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u''} [Category.{v''} E] (F : C ⥤ D) (P : D ⥤ E) (Q : C ⥤ E) : Prop :=
  ∀ (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (ε : 𝟭 E ≅ 𝟭 E),
    Preserves Q α ε → Preserves P β ε → Preserves F α β

/-- The literal original evaluation square and faithfulness supply the action transport. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismEvaluation.lean:35-40"
  "adaptation" "The original faithful-evaluation identity-action transport"]
theorem evaluationPreserves_of_eq {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
    (F : C ⥤ D) (P : D ⥤ E) [P.Faithful] (Q : C ⥤ E) (h : F ⋙ P = Q) :
    EvaluationPreserves F P Q := by
  intro α β ε ha hb S
  exact NatTrans.congr_app (whisker_hom_eq_of_evaluation F P Q h α β ε ha hb) S

/-- Forward component compatibility is the exact original equality of whiskered actions. -/
theorem Preserves.whisker {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {α : 𝟭 C ≅ 𝟭 C} {β : 𝟭 D ≅ 𝟭 D} (h : Preserves F α β) :
    Functor.whiskerRight α.hom F = Functor.whiskerLeft F β.hom := by
  apply NatTrans.ext
  funext S
  exact h S

end CategoryTheory.Functor.IdentityAutomorphism

