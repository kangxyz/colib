/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.Colimits
public import Colib.CategoryTheory.Prespectrum.LevelFactorization
public import Colib.Util.References
public import Colib.CategoryTheory.SmallObject.Accessible
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
# Small objects for free sequential prespectra

If suspension preserves the relevant colimits, evaluation preserves them too.
The free/evaluation adjunction then carries presentable generators to
presentable prespectra. This discharges the small-object condition for their
free maps under the stated category-size and colimit hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
/-- A prespectrum map is determined by its countable family of level maps. -/
instance [LocallySmall.{w} C] : LocallySmall.{w} (SequentialPrespectrum S) where
  hom_small X Y := by
    apply small_of_injective (f := fun f : X ⟶ Y ↦ f.app)
    intro f g h
    exact Hom.ext h

variable [HasInitial C] [PreservesColimit (Functor.empty.{0} C) S]
variable [HasColimitsOfSize.{w, w} C] [PreservesColimitsOfSize.{w, w} S]
/-- Colimits of the stated size are formed levelwise. -/
instance : HasColimitsOfSize.{w, w} (SequentialPrespectrum S) where
  has_colimits_of_shape := fun _ ↦ inferInstance

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

omit [HasInitial C] [PreservesColimit (Functor.empty.{0} C) S] in
/-- Evaluation preserves κ-filtered colimits because these colimits are levelwise. -/
theorem evaluation_isCardinalAccessible (n : ℕ) :
    (evaluation (S := S) n).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by infer_instance

/-- A free prespectrum on a κ-presentable object is κ-presentable. -/
theorem freeAt_isCardinalPresentable (n : ℕ) (X : C) [IsCardinalPresentable X κ] :
    IsCardinalPresentable ((freeAt (S := S) n).obj X) κ := by
  have : (evaluation (S := S) n).IsCardinalAccessible κ :=
    evaluation_isCardinalAccessible κ n
  exact (freeAtAdjunction (S := S) n).isCardinalPresentable_leftAdjoint_obj κ X

/-- A free prespectrum on a presentable object is presentable. -/
theorem freeAt_isPresentable (n : ℕ) (X : C) (hX : IsPresentable.{w} X) :
    IsPresentable.{w} ((freeAt (S := S) n).obj X) := by
  obtain ⟨ρ, hρ, hXρ⟩ := hX.exists_cardinal
  have : Fact ρ.IsRegular := hρ
  have : IsCardinalPresentable X ρ := hXρ
  exact ⟨ρ, hρ, freeAt_isCardinalPresentable ρ n X⟩

variable {ι : Type w} {A B : ι → C} (i : ∀ a, A a ⟶ B a)
variable [∀ a, IsCardinalPresentable (A a) κ]
variable [LocallySmall.{w} C]
variable [OrderBot κ.ord.ToType]

/-- Uniform presentability of the original domains proves the free family
meets Mathlib's cardinal small-object conditions. -/
theorem freeAtMaps_isCardinalForSmallObjectArgument :
    (freeAtMaps (S := S) i).IsCardinalForSmallObjectArgument κ where
  isSmall := by
    unfold freeAtMaps
    infer_instance
  preservesColimit {P Q X Y} j hj f hf := by
    have : IsCardinalPresentable P κ := by
      cases hj with
      | mk x => exact freeAt_isCardinalPresentable κ x.1 (A x.2)
    have : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (Opposite.op P)) :=
      preservesColimitsOfShape_of_isCardinalPresentable P κ κ.ord.ToType
    infer_instance

omit [OrderBot κ.ord.ToType] in
include κ in
/-- Consequently the free family admits the small object argument. -/
theorem freeAtMaps_hasSmallObjectArgument :
    (freeAtMaps (S := S) i).HasSmallObjectArgument.{w} := by
  have : Nonempty κ.ord.ToType := by simpa using (Fact.out : κ.IsRegular).ne_zero
  have : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance, freeAtMaps_isCardinalForSmallObjectArgument κ i⟩

omit [OrderBot κ.ord.ToType] in
include κ in
/-- Uniformly presentable base domains give the projective level functorial
factorization, with right class the levelwise right class of the generators. -/
theorem levelwise_hasFunctorialFactorization_of_presentable :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := S) (MorphismProperty.ofHoms i).rlp).llp
      (levelwise (S := S) (MorphismProperty.ofHoms i).rlp) := by
  have : (freeAtMaps (S := S) i).HasSmallObjectArgument.{w} :=
    freeAtMaps_hasSmallObjectArgument κ i
  exact levelwise_hasFunctorialFactorization i

omit [OrderBot κ.ord.ToType] [∀ a, IsCardinalPresentable (A a) κ] in
/-- A small family of individually presentable base domains suffices: a common
regular cardinal is chosen by the native small-object construction. -/
theorem freeAtMaps_hasSmallObjectArgument_of_presentable
    (hA : ∀ a, IsPresentable.{w} (A a)) :
    (freeAtMaps (S := S) i).HasSmallObjectArgument.{w} := by
  unfold freeAtMaps
  exact MorphismProperty.hasSmallObjectArgument_ofHoms_of_presentable
    (fun x : ℕ × ι ↦ (freeAt (S := S) x.1).map (i x.2))
    (fun x ↦ freeAt_isPresentable x.1 (A x.2) (hA x.2))

omit [OrderBot κ.ord.ToType] [∀ a, IsCardinalPresentable (A a) κ] in
/-- Individually presentable base domains give the projective level functorial
factorization, without a chosen common presentability cardinal. -/
theorem levelwise_hasFunctorialFactorization_of_domains_presentable
    (hA : ∀ a, IsPresentable.{w} (A a)) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := S) (MorphismProperty.ofHoms i).rlp).llp
      (levelwise (S := S) (MorphismProperty.ofHoms i).rlp) := by
  have : (freeAtMaps (S := S) i).HasSmallObjectArgument.{w} :=
    freeAtMaps_hasSmallObjectArgument_of_presentable i hA
  exact levelwise_hasFunctorialFactorization i

end CategoryTheory.SequentialPrespectrum

attribute [colib_tag "COL-1229"]
  CategoryTheory.SequentialPrespectrum.freeAtMaps_hasSmallObjectArgument_of_presentable
  CategoryTheory.SequentialPrespectrum.levelwise_hasFunctorialFactorization_of_domains_presentable

attribute [colib_ref "Hovey2001Spectra" "Section 1, Theorem 1.14, pp. 7–8"
  "ingredient" "The small object argument for the free images of the level generators"]
  CategoryTheory.SequentialPrespectrum.levelwise_hasFunctorialFactorization_of_domains_presentable
