/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexLaws
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-! # Original evaluation-lifted identity actions under section restriction -/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexUnit.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.GrothendieckSections
universe u v w z u' v'
namespace CategoryTheory.SectionChangeIndex
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D)

/-- The pulled-back evaluation with its unchanged original fiber as explicit codomain. -/
def pulledEvaluation (c : C) :
    CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget (pullback F K)) c ⥤ F.obj ⟨K.obj c⟩ :=
  originalEvaluation (pullback F K) c

instance pulledEvaluation_isEquivalence (c : C) :
    (pulledEvaluation F K c).IsEquivalence :=
  inferInstanceAs (originalEvaluation (pullback F K) c).IsEquivalence

/-- Restriction preserves a fixed fiber automorphism lifted through both original evaluations. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexUnit.lean:34"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem restriction_lift_preserves (c : C)
    (e : 𝟭 (F.obj ⟨K.obj c⟩) ≅ 𝟭 (F.obj ⟨K.obj c⟩)) :
    Preserves (underFunctor F K c)
      (lift (originalEvaluation F (K.obj c)) e)
      (lift (pulledEvaluation F K c) e) :=
  evaluationPreserves_of_eq (underFunctor F K c)
    (pulledEvaluation F K c) (originalEvaluation F (K.obj c))
    (evaluation F K c) _ _ e
    (map_lift_hom _ e) (map_lift_hom _ e)

end CategoryTheory.SectionChangeIndex
