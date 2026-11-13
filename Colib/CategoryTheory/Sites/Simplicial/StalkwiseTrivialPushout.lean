/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantSmash
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
import Colib.Topology.Realization.MapWeakEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Pushouts of stalkwise trivial monomorphisms

The original site fibers preserve pushouts and monomorphisms. Gluing the
realized pushout square shows that the pushed-out map is again stalkwise
trivial. These are the pushouts in the pointed presheaf category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)

/-- A pushout along a monomorphism transports a realization weak equivalence on a site fiber. -/
theorem isRealizationWeakEquivalence_presheafFiber_of_isPushout (Φ : J.Point.{w})
    {A B X Y : Cᵒᵖ ⥤ SSet.{w}} {i : A ⟶ B} {f : A ⟶ X} {g : B ⟶ Y} {j : X ⟶ Y}
    [Mono i] (sq : IsPushout i f g j)
    (hi : SSet.IsRealizationWeakEquivalence ((Φ.presheafFiber (A := SSet.{w})).map i)) :
    SSet.IsRealizationWeakEquivalence ((Φ.presheafFiber (A := SSet.{w})).map j) := by
  let E := Φ.presheafFiber (A := SSet.{w})
  let hE : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits (Φ.presheafFiber (A := SSet.{w})))
  let : PreservesLimitsOfShape WalkingCospan E := hE.preservesFiniteLimits WalkingCospan
  let : PreservesLimit (cospan i i) E := PreservesLimitsOfShape.preservesLimit
  let : Mono (E.map i) := preserves_mono_of_preservesLimit E i
  let t := sq.map E
  exact SSet.IsRealizationWeakEquivalence.pushout
    (IsPushout.of_id_fst (f := E.map f)) t
    (𝟙 _) (E.map i) (𝟙 _) (E.map j)
    rfl (by rw [Category.comp_id, Category.id_comp]) t.w.symm rfl
    (SSet.IsRealizationWeakEquivalence.id _) hi (SSet.IsRealizationWeakEquivalence.id _)

/-- A pushout of a stalkwise trivial monomorphism is a stalkwise trivial monomorphism. -/
theorem stalkwiseTrivialMonomorphisms_of_isPushout
    {A B X Y : PointedSimplicialPresheaf.{w} C}
    {i : A ⟶ B} {f : A ⟶ X} {g : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f g j) (hi : stalkwiseTrivialMonomorphisms C J i) :
    stalkwiseTrivialMonomorphisms C J j := by
  let F := forget.{w} C
  let : Mono i := hi.1
  let : Mono i.right := Under.mono_right_of_mono i
  have hm : Mono j.right := by
    let W := MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{w})
    let : W.IsStableUnderCobaseChange := by
      change (MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderCobaseChange
      rw [← MorphismProperty.functorCategory_monomorphisms]
      infer_instance
    exact W.of_isPushout (sq.map F).flip (inferInstanceAs (Mono i.right))
  let : Mono j.right := hm
  refine ⟨Under.mono_of_mono_right j, fun Φ => ?_⟩
  let : Mono (F.map i) := inferInstanceAs (Mono i.right)
  exact isRealizationWeakEquivalence_presheafFiber_of_isPushout C J Φ (sq.map F) (hi.2 Φ)

instance : (stalkwiseTrivialMonomorphisms.{w} C J).IsStableUnderCobaseChange where
  of_isPushout sq hi := stalkwiseTrivialMonomorphisms_of_isPushout C J sq.flip hi

end CategoryTheory.PointedSimplicialPresheaf
