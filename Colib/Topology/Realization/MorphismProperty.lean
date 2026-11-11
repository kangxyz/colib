/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.MapWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# The morphism property of realization weak equivalences

The weak equivalence is the existing predicate on the actual realization map,
including its component-surjectivity clause. This file packages its identity,
composition and two-of-three laws for categorical localization. It does not
construct a model category structure on simplicial sets.
-/

@[expose] public section

open CategoryTheory

universe u

namespace SSet

namespace IsRealizationWeakEquivalence

/-- The identity simplicial map is a realization weak equivalence. -/
theorem id (X : SSet.{u}) : IsRealizationWeakEquivalence (𝟙 X) :=
  of_isIso _

/-- Composition retains the original realized maps. -/
theorem comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsRealizationWeakEquivalence g) (hf : IsRealizationWeakEquivalence f) :
    IsRealizationWeakEquivalence (f ≫ g) := by
  change Topology.IsWeakHomotopyEquivalence (SSet.toTop.map (f ≫ g)).hom
  rw [Functor.map_comp, TopCat.hom_comp]
  exact Topology.IsWeakHomotopyEquivalence.comp hg hf

/-- Cancel the first realized weak equivalence in a composite. -/
theorem of_comp_left {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : IsRealizationWeakEquivalence (f ≫ g))
    (hf : IsRealizationWeakEquivalence f) : IsRealizationWeakEquivalence g := by
  apply Topology.IsWeakHomotopyEquivalence.of_comp_left ?_ hf
  simpa only [IsRealizationWeakEquivalence, Functor.map_comp, TopCat.hom_comp] using hfg

/-- Cancel the second realized weak equivalence in a composite. -/
theorem of_comp_right {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : IsRealizationWeakEquivalence (f ≫ g))
    (hg : IsRealizationWeakEquivalence g) : IsRealizationWeakEquivalence f := by
  apply Topology.IsWeakHomotopyEquivalence.of_comp_right ?_ hg
  simpa only [IsRealizationWeakEquivalence, Functor.map_comp, TopCat.hom_comp] using hfg

end IsRealizationWeakEquivalence

/-- The class of simplicial maps whose actual realizations are weak homotopy
equivalences, including components and all based homotopy groups. -/
def realizationWeakEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ IsRealizationWeakEquivalence f

@[simp]
theorem realizationWeakEquivalences_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences f ↔ IsRealizationWeakEquivalence f := Iff.rfl

instance : realizationWeakEquivalences.{u}.IsMultiplicative where
  id_mem := IsRealizationWeakEquivalence.id
  comp_mem _ _ hf hg := IsRealizationWeakEquivalence.comp hg hf

instance : realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  of_postcomp _ _ hg hfg := IsRealizationWeakEquivalence.of_comp_right hfg hg
  of_precomp _ _ hf hfg := IsRealizationWeakEquivalence.of_comp_left hfg hf

/-- Every simplicial isomorphism belongs to the fixed realization weak class. -/
theorem realizationWeakEquivalences_of_isIso {X Y : SSet.{u}}
    (f : X ⟶ Y) [IsIso f] : realizationWeakEquivalences f :=
  IsRealizationWeakEquivalence.of_isIso f

instance : realizationWeakEquivalences.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf ↦ by
      let : IsIso f := hf
      exact realizationWeakEquivalences_of_isIso f)

end SSet
