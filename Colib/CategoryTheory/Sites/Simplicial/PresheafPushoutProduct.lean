/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedTrivialGenerators
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import Colib.Topology.Realization.ProductWeakEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adhesive.PushoutProduct
import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# Pushout-products of simplicial presheaf monomorphisms

The unpointed cartesian pushout-product preserves monomorphisms.
If one factor is stalkwise weak, the product comparison and gluing
give weakness of the actual pushout-product at every site point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)

omit [LocallySmall.{w} C] in
/-- The native cartesian pushout-product of two presheaf monomorphisms is monic. -/
theorem mono_presheafPushoutProduct
    {A B X Y : Cᵒᵖ ⥤ SSet.{w}} (f : A ⟶ B) (g : X ⟶ Y) [Mono f] [Mono g] :
    Mono (Arrow.mk f □ Arrow.mk g).hom := by
  let : Mono (Arrow.mk f).hom := inferInstanceAs (Mono f)
  let : Mono (Arrow.mk g).hom := inferInstanceAs (Mono g)
  infer_instance

private theorem weak_tensorHom_at (Φ : J.Point.{w})
    {A B X Y : Cᵒᵖ ⥤ SSet.{w}} {f : A ⟶ B} {g : X ⟶ Y}
    (hf : SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f))
    (hg : SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map g)) :
    SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (f ⊗ₘ g)) := by
  let F := Φ.presheafFiber (A := SSet.{w})
  let : AB5OfSize.{w, w} SSet.{w} :=
    ⟨fun T _ _ => inferInstanceAs
      (HasExactColimitsOfShape T (SimplexCategoryᵒᵖ ⥤ Type w))⟩
  let h : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (Φ.presheafFiber (A := SSet.{w})))
  let : PreservesLimitsOfShape (Discrete WalkingPair) F := h.preservesFiniteLimits _
  let : PreservesLimit (pair A X) F := PreservesLimitsOfShape.preservesLimit
  let : PreservesLimit (pair B Y) F := PreservesLimitsOfShape.preservesLimit
  exact SSet.IsRealizationWeakEquivalence.of_iso_square _ _
    (CartesianMonoidalCategory.prodComparisonIso F A X)
    (CartesianMonoidalCategory.prodComparisonIso F B Y)
    (by simpa only [CartesianMonoidalCategory.prodComparisonIso_hom] using
      (CartesianMonoidalCategory.prodComparison_natural F f g)) (hf.tensorHom hg)

/-- The original cartesian pushout-product of a weak monomorphism with
any map is weak on every site fiber. -/
theorem weak_presheafFiber_pushoutProduct (Φ : J.Point.{w})
    {A B X Y : Cᵒᵖ ⥤ SSet.{w}} (f : A ⟶ B) (g : X ⟶ Y) [Mono f]
    (hf : SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f)) :
    SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (Arrow.mk f □ Arrow.mk g).hom) := by
  let F := Φ.presheafFiber (A := SSet.{w})
  let d := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor (Cᵒᵖ ⥤ SSet.{w})) f g
  let : Mono (f ▷ X) := (tensorRight X).map_mono f
  let : Mono (((curriedTensor (Cᵒᵖ ⥤ SSet.{w})).map f).app X) :=
    inferInstanceAs (Mono (f ▷ X))
  have h₁ : SSet.IsRealizationWeakEquivalence (F.map (f ▷ X)) := by
    rw [← tensorHom_id]
    exact weak_tensorHom_at J Φ hf ((F.map_id X).symm ▸
      SSet.IsRealizationWeakEquivalence.id (F.obj X))
  have h₂ : SSet.IsRealizationWeakEquivalence (F.map (f ▷ Y)) := by
    rw [← tensorHom_id]
    exact weak_tensorHom_at J Φ hf ((F.map_id Y).symm ▸
      SSet.IsRealizationWeakEquivalence.id (F.obj Y))
  have hd : SSet.IsRealizationWeakEquivalence (F.map d.inr) :=
    isRealizationWeakEquivalence_presheafFiber_of_isPushout C J Φ d.isPushout h₁
  have h : SSet.IsRealizationWeakEquivalence
      (F.map (((curriedTensor (Cᵒᵖ ⥤ SSet.{w})).map f).app Y)) := h₂
  change SSet.IsRealizationWeakEquivalence (F.map d.ι)
  rw [← d.inr_ι, F.map_comp] at h
  exact h.of_comp_left hd

omit [LocallySmall.{w} C] in
/-- Free pointing of the actual cartesian pushout-product preserves
stalkwise triviality in its first factor. -/
theorem stalkwiseTrivialMonomorphisms_free_pushoutProduct
    {A B X Y : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B) (g : X ⟶ Y) [Mono f] [Mono g]
    (hf : ∀ Φ : J.Point.{max u v}, SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f)) :
    stalkwiseTrivialMonomorphisms C J ((free C).map (Arrow.mk f □ Arrow.mk g).hom) := by
  let : Mono (Arrow.mk f □ Arrow.mk g).hom := mono_presheafPushoutProduct f g
  let : LocallySmall.{max u v} C := CategoryTheory.locallySmall_max
  exact stalkwiseTrivialMonomorphisms_free_map C J _ fun Φ =>
    weak_presheafFiber_pushoutProduct J Φ f g (hf Φ)

end CategoryTheory.PointedSimplicialPresheaf
