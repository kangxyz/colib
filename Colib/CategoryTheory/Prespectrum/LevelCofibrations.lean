/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.SmallObject

/-!
# Projective cofibrations and levelwise classes

When a base class is stable under the small-object operations and preserved
by suspension, the generated projective left class is levelwise in that base
class.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory.SequentialPrespectrum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
variable [HasInitial C] [PreservesColimit (Functor.empty.{0} C) S]
variable [HasColimitsOfSize.{w, w} C] [PreservesColimitsOfSize.{w, w} S]
variable (P : MorphismProperty C)

/-- A levelwise class inherits the two-out-of-three property. -/
instance [P.HasTwoOutOfThreeProperty] : (levelwise (S := S) P).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg n := P.comp_mem (f.app n) (g.app n) (hf n) (hg n)
  of_postcomp f g hg hfg n := P.of_postcomp (f.app n) (g.app n) (hg n) (hfg n)
  of_precomp f g hf hfg n := P.of_precomp (f.app n) (g.app n) (hf n) (hfg n)

/-- Retracts of levelwise maps remain levelwise in a retract-stable class. -/
instance [P.IsStableUnderRetracts] : (levelwise (S := S) P).IsStableUnderRetracts where
  of_retract h hg n := P.of_retract (h.map (evaluation n)) (hg n)

/-- Evaluation carries pushouts to pushouts, so levelwise classes inherit
stability under cobase change. -/
instance [P.IsStableUnderCobaseChange] : (levelwise (S := S) P).IsStableUnderCobaseChange where
  of_isPushout sq hf n := by
    let : PreservesColimitsOfSize.{0, 0} S :=
      preservesSmallestColimits_of_preservesColimits S
    exact P.of_isPushout (sq.map (evaluation n)) (hf n)

/-- Levelwise classes inherit stable colimits of each shape preserved by suspension. -/
instance {J : Type w} [Category.{w} J] [P.IsStableUnderColimitsOfShape J] :
    (levelwise (S := S) P).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ n :=
    P.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ evaluation n) (X₂ ⋙ evaluation n) _ _
        (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂)
        (Functor.whiskerRight f (evaluation n)) (fun j ↦ hf j n) (φ.app n)
        (fun j ↦ congrArg (fun g ↦ g.app n) (hφ j)))

instance [P.IsStableUnderCoproducts.{w}] :
    (levelwise (S := S) P).IsStableUnderCoproducts.{w} where

/-- Levelwise classes inherit stability under transfinite compositions. -/
instance [P.IsStableUnderTransfiniteComposition.{w}] :
    (levelwise (S := S) P).IsStableUnderTransfiniteComposition.{w} where
  isStableUnderTransfiniteCompositionOfShape I := ⟨fun _ _ f hf n ↦ by
    let F := evaluation (S := S) n
    let : PreservesWellOrderContinuousOfShape I F := ⟨fun j hj ↦ by infer_instance⟩
    obtain ⟨t⟩ := hf
    have h : (P.inverseImage F).TransfiniteCompositionOfShape I f :=
      t.ofLE (fun _ _ _ hg ↦ hg n)
    exact P.transfiniteCompositionsOfShape_le I _ ⟨h.map⟩⟩

/-- The projective left class is levelwise in any saturated base class
containing the generators and preserved by suspension. -/
theorem projectiveLeft_le_levelwise [P.IsMultiplicative] [P.IsStableUnderRetracts]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderCoproducts.{w}]
    [P.IsStableUnderTransfiniteComposition.{w}]
    (hS : ∀ ⦃A B : C⦄ (f : A ⟶ B), P f → P (S.map f))
    {ι : Type w} {A B : ι → C} (i : ∀ a, A a ⟶ B a)
    (hi : ∀ a, P (i a))
    [(freeAtMaps (S := S) i).HasSmallObjectArgument.{w}] :
    (levelwise (S := S) (MorphismProperty.ofHoms i).rlp).llp ≤ levelwise P := by
  rw [levelwise_llp_eq_retracts i]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  intro _ _ f hf
  cases hf with
  | mk x => exact fun m ↦ freeAt_map_app_mem P hS (i x.2) (hi x.2) x.1 m

/-- Presentable generating domains discharge the small-object hypothesis in
the levelwise comparison. -/
theorem projectiveLeft_le_levelwise_of_presentable [LocallySmall.{w} C]
    [P.IsMultiplicative] [P.IsStableUnderRetracts] [P.IsStableUnderCobaseChange]
    [P.IsStableUnderCoproducts.{w}] [P.IsStableUnderTransfiniteComposition.{w}]
    (hS : ∀ ⦃A B : C⦄ (f : A ⟶ B), P f → P (S.map f))
    {ι : Type w} {A B : ι → C} (i : ∀ a, A a ⟶ B a)
    (hi : ∀ a, P (i a)) (hA : ∀ a, IsPresentable.{w} (A a)) :
    (levelwise (S := S) (MorphismProperty.ofHoms i).rlp).llp ≤ levelwise P := by
  have : (freeAtMaps (S := S) i).HasSmallObjectArgument.{w} :=
    freeAtMaps_hasSmallObjectArgument_of_presentable i hA
  exact projectiveLeft_le_levelwise P hS i hi

end CategoryTheory.SequentialPrespectrum
