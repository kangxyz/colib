/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Functor.BoundedTypeValues
public import Colib.CategoryTheory.Sites.Simplicial.BoundedFiberSupport
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialPushout
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# A small family of bounded trivial monomorphisms

The sectionwise model in a fixed carrier gives a small index type for
bounded simplicial presheaves and their arrows. Free pointing takes
the chosen trivial arrows to the original pointed category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite FunctorToTypes

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) (κ : Cardinal.{max u v})

/-- The fixed-carrier models for bounded unpointed simplicial presheaves. -/
abbrev BoundedPresheafModel : Type (max u v) :=
  (Cᵒᵖ × SimplexCategoryᵒᵖ) ⥤ SubsetCategory κ.ord.ToType

/-- Interpret a bounded model by currying the original section functor. -/
def boundedPresheafModelObj (B : BoundedPresheafModel C κ) : Cᵒᵖ ⥤ SSet.{max u v} :=
  Functor.curry.obj (B ⋙ subsetInclusion κ.ord.ToType)

/-- Bounded section spaces have fixed-carrier models in the original
coefficient universe. -/
theorem exists_boundedPresheafModel_iso (X : Cᵒᵖ ⥤ SSet.{max u v})
    (hX : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (X.obj q.1).obj q.2) κ) :
    ∃ B : BoundedPresheafModel C κ, Nonempty (X ≅ boundedPresheafModelObj C κ B) := by
  let F := Functor.uncurry.obj X
  have h (q : Cᵒᵖ × SimplexCategoryᵒᵖ) : HasCardinalLT (F.obj q) κ :=
    hX.of_injective (Sigma.mk q) sigma_mk_injective
  exact ⟨boundedModel F κ h,
    ⟨(Functor.currying.unitIso.app X) ≪≫ Functor.curry.mapIso (boundedModelIso F κ h)⟩⟩

/-- The small set of arrows between fixed-carrier models that are weak
monomorphisms on the actual site fibers. -/
abbrev BoundedTrivialArrow : Type (max u v) :=
  {q : Σ A B : BoundedPresheafModel C κ,
      boundedPresheafModelObj C κ A ⟶ boundedPresheafModelObj C κ B //
    Mono q.2.2 ∧ ∀ Φ : J.Point.{max u v},
      SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map q.2.2)}

/-- The morphism property consisting of freely pointed bounded representatives. -/
def boundedTrivialGenerators : MorphismProperty (PointedSimplicialPresheaf.{max u v} C) :=
  MorphismProperty.ofHoms (fun q : BoundedTrivialArrow C J κ => (free C).map q.val.2.2)

/-- Freely pointing an unpointed trivial monomorphism is the actual
basepoint-adjoining pushout, which is again stalkwise trivial. -/
theorem stalkwiseTrivialMonomorphisms_free_map
    {X Y : Cᵒᵖ ⥤ SSet.{max u v}} (f : X ⟶ Y) [Mono f]
    (hf : ∀ Φ : J.Point.{max u v}, SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f)) :
    stalkwiseTrivialMonomorphisms C J ((free C).map f) := by
  let t := (⊤_ (Cᵒᵖ ⥤ SSet.{max u v}))
  let sq := (IsPushout.of_coprod_inl_with_id f t).flip
  let W := MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{max u v})
  let : W.IsStableUnderCobaseChange := by
    change (MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{max u v})).IsStableUnderCobaseChange
    rw [← MorphismProperty.functorCategory_monomorphisms]
    infer_instance
  let : Mono (coprod.map f (𝟙 t)) :=
    W.of_isPushout sq.flip (inferInstanceAs (Mono f))
  let : Mono ((free C).map f).right := inferInstanceAs (Mono (coprod.map f (𝟙 t)))
  refine ⟨Under.mono_of_mono_right ((free C).map f), fun Φ => ?_⟩
  exact isRealizationWeakEquivalence_presheafFiber_of_isPushout C J Φ sq (hf Φ)

/-- Each chosen generating map belongs to the original pointed trivial class. -/
theorem boundedTrivialGenerators_le :
    boundedTrivialGenerators C J κ ≤ stalkwiseTrivialMonomorphisms C J := by
  intro A B f h
  obtain ⟨q⟩ := h
  let : Mono q.val.2.2 := q.property.1
  exact stalkwiseTrivialMonomorphisms_free_map C J _ q.property.2

/-- Free pointing a trivial mono with bounded domain and codomain yields
a map in the isomorphism closure of the chosen generator family. -/
theorem isoClosure_boundedTrivialGenerators
    {X Y : Cᵒᵖ ⥤ SSet.{max u v}} (f : X ⟶ Y) [Mono f]
    (hf : ∀ Φ : J.Point.{max u v}, SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f))
    (hX : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (X.obj q.1).obj q.2) κ)
    (hY : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (Y.obj q.1).obj q.2) κ) :
    (boundedTrivialGenerators C J κ).isoClosure ((free C).map f) := by
  obtain ⟨A, ⟨eA⟩⟩ := exists_boundedPresheafModel_iso C κ X hX
  obtain ⟨B, ⟨eB⟩⟩ := exists_boundedPresheafModel_iso C κ Y hY
  let g := eA.inv ≫ f ≫ eB.hom
  let e : Arrow.mk g ≅ Arrow.mk f := Arrow.isoMk eA.symm eB.symm (by simp [g])
  have hg : Mono g ∧ ∀ Φ : J.Point.{max u v},
      SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map g) :=
    ⟨inferInstanceAs (Mono (eA.inv ≫ f ≫ eB.hom)), fun Φ =>
      (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).obj Φ.presheafFiber).mapIso e)).2 (hf Φ)⟩
  let q : BoundedTrivialArrow C J κ := ⟨⟨A, B, g⟩, hg⟩
  exact ⟨_, _, (free C).map g, ⟨q⟩, ⟨((Functor.mapArrowFunctor _ _).obj (free C)).mapIso e⟩⟩

end CategoryTheory.PointedSimplicialPresheaf
