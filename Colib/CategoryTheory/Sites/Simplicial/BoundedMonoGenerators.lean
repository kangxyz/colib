/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedTrivialLifting
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresentability
public import Colib.CategoryTheory.SmallObject.Accessible
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# A small generating family for simplicial presheaf monomorphisms

At a missing section, its generated subpresheaf is bounded by the
original restriction arrows. Its intersection with a partial lift is
bounded by the same cardinal. Thus the same sectionwise extension
argument as for stalkwise trivial monomorphisms gives a small family
which tests all monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite SimplicialSubpresheaf
open Stacks.Sites.UniverseBridge

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{max u v})

/-- Monomorphisms between the original fixed-carrier models. -/
abbrev BoundedMonoArrow : Type (max u v) :=
  {q : Σ A B : BoundedPresheafModel C κ,
      boundedPresheafModelObj C κ A ⟶ boundedPresheafModelObj C κ B // Mono q.2.2}

/-- Freely pointed representatives of the bounded monomorphisms. -/
def boundedMonoGenerators : MorphismProperty (PointedSimplicialPresheaf.{max u v} C) :=
  MorphismProperty.ofHoms (fun q : BoundedMonoArrow C κ => (free C).map q.val.2.2)

/-- Free pointing preserves the original monomorphisms. -/
theorem mono_free_map {X Y : Cᵒᵖ ⥤ SSet.{max u v}} (f : X ⟶ Y) [Mono f] :
    Mono ((free C).map f) := by
  let t := (⊤_ (Cᵒᵖ ⥤ SSet.{max u v}))
  let W := MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{max u v})
  let : W.IsStableUnderCobaseChange := by
    change (MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{max u v})).IsStableUnderCobaseChange
    rw [← MorphismProperty.functorCategory_monomorphisms]
    infer_instance
  let : Mono ((free C).map f).right :=
    W.of_isPushout (IsPushout.of_coprod_inl_with_id f t) (inferInstanceAs (Mono f))
  exact Under.mono_of_mono_right _

/-- Each actual generator is a monomorphism. -/
theorem boundedMonoGenerators_le :
    boundedMonoGenerators C κ ≤ MorphismProperty.monomorphisms _ := by
  intro A B f h
  obtain ⟨q⟩ := h
  let : Mono q.val.2.2 := q.property
  exact mono_free_map C _

/-- The original free pointing of a bounded mono is isomorphic to a generator. -/
theorem isoClosure_boundedMonoGenerators
    {X Y : Cᵒᵖ ⥤ SSet.{max u v}} (f : X ⟶ Y) [Mono f]
    (hX : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (X.obj q.1).obj q.2) κ)
    (hY : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (Y.obj q.1).obj q.2) κ) :
    (boundedMonoGenerators C κ).isoClosure ((free C).map f) := by
  obtain ⟨A, ⟨eA⟩⟩ := exists_boundedPresheafModel_iso C κ X hX
  obtain ⟨B, ⟨eB⟩⟩ := exists_boundedPresheafModel_iso C κ Y hY
  let g := eA.inv ≫ f ≫ eB.hom
  let e : Arrow.mk g ≅ Arrow.mk f := Arrow.isoMk eA.symm eB.symm (by simp [g])
  let q : BoundedMonoArrow C κ := ⟨⟨A, B, g⟩, inferInstanceAs (Mono (eA.inv ≫ f ≫ eB.hom))⟩
  exact ⟨_, _, (free C).map g, ⟨q⟩, ⟨((Functor.mapArrowFunctor _ _).obj (free C)).mapIso e⟩⟩

/-- The chosen small family tests right lifting against all pointed monomorphisms. -/
theorem rlp_boundedMonoGenerators_eq
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    (boundedMonoGenerators C κ).rlp = (MorphismProperty.monomorphisms _).rlp := by
  apply le_antisymm ?_ (MorphismProperty.antitone_rlp (boundedMonoGenerators_le C κ))
  intro X Y p hp P Q i hi
  let : Mono i := hi
  let : Mono i.right := Under.mono_right_of_mono i
  apply hasLiftingProperty_of_right C
  apply hasLiftingProperty_inclusion_range C i.right p.right
  refine hasLiftingProperty_inclusion_of_extend_of_property (fun _ => True) trivial
    (fun _ _ _ _ => trivial) ?_
  intro B _ _ q s
  let D : Subpresheaf Q.right := ofSectionGen s
  have hD : HasBoundedSections D κ := Subfunctor.hasCardinalLT_totalSections_ofSectionGen s κ (hC q)
  let h : B ⊓ D ≤ D := inf_le_right
  let j : toPresheaf (B ⊓ D) ⟶ toPresheaf D := SimplicialSubpresheaf.homOfLE h
  let : Mono j := mono_of_mono_fac (homOfLE_inclusion h)
  obtain ⟨_, _, g, hg, ⟨e⟩⟩ := isoClosure_boundedMonoGenerators C κ j
    (hasBoundedSections_of_le h hD) hD
  have hl := (HasLiftingProperty.iff_of_arrow_iso_left e p).1 (hp g hg)
  exact ⟨D, mem_ofSectionGen_self s, trivial, (freeForgetAdjunction C).hasLiftingProperty_iff j p
    |>.1 hl⟩

/-- The bounded mono family admits the native small object argument. -/
theorem hasSmallObjectArgument_boundedMonoGenerators :
    MorphismProperty.HasSmallObjectArgument.{max u v} (boundedMonoGenerators C κ) := by
  let : LocallySmall.{max u v} (PointedSimplicialPresheaf.{max u v} C) :=
    CategoryTheory.locallySmall_self _
  exact MorphismProperty.hasSmallObjectArgument_ofHoms_of_presentable
    (fun q : BoundedMonoArrow C κ => (free C).map q.val.2.2)
    (fun _ => isPresentable_pointedSimplicialPresheaf _)

end CategoryTheory.PointedSimplicialPresheaf
