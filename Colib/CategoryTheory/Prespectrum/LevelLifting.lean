/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.Free
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Levelwise lifting for sequential prespectra

The free-at-level adjunction identifies lifting against the free images of a
family of maps with lifting against the original family in every degree.
This is the lifting calculation underlying the projective level structure;
it does not assert the existence of a model structure.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
variable [HasInitial C] [PreservesColimit (Functor.empty.{0} C) S]

/-- Lifting against a free map is lifting against the original map in that degree. -/
theorem freeAt_hasLiftingProperty_iff (n : ℕ) {A B : C} (i : A ⟶ B)
    {X Y : SequentialPrespectrum S} (p : X ⟶ Y) :
    HasLiftingProperty ((freeAt (S := S) n).map i) p ↔
      HasLiftingProperty i (p.app n) :=
  (freeAtAdjunction (S := S) n).hasLiftingProperty_iff i p

/-- The family of free images of generating maps in all degrees. -/
def freeAtMaps {ι : Type w} {A B : ι → C} (i : ∀ a, A a ⟶ B a) :
    MorphismProperty (SequentialPrespectrum S) :=
  MorphismProperty.ofHoms (fun x : ℕ × ι ↦ (freeAt (S := S) x.1).map (i x.2))

/-- Right lifting against the free generators is exactly levelwise right lifting
against the original generators. -/
theorem freeAtMaps_rlp_iff {ι : Type w} {A B : ι → C} (i : ∀ a, A a ⟶ B a)
    {X Y : SequentialPrespectrum S} (p : X ⟶ Y) :
    (freeAtMaps (S := S) i).rlp p ↔
      ∀ n, (MorphismProperty.ofHoms i).rlp (p.app n) := by
  constructor
  · intro h n _ _ j hj
    cases hj with
    | mk a =>
      exact (freeAt_hasLiftingProperty_iff n (i a) p).1 (h _ ⟨(n, a)⟩)
  · intro h _ _ j hj
    cases hj with
    | mk x =>
      exact (freeAt_hasLiftingProperty_iff x.1 (i x.2) p).2 (h x.1 _ ⟨x.2⟩)

end CategoryTheory.SequentialPrespectrum
