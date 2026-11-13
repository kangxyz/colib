/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashFunctor
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Colib.CategoryTheory.Sites.Simplicial.SmashMonomorphism
import Colib.CategoryTheory.Sites.Simplicial.SmashWeakEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Lifting against stalkwise trivial monomorphisms

Smash with a pointed presheaf preserves the monomorphisms that are
stalkwise weak equivalences. By the pointed internal Hom adjunction,
the right lifting property for this class passes to the internal Hom.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

/-- Monomorphisms that are weak equivalences on the actual site fibers. -/
abbrev stalkwiseTrivialMonomorphisms : MorphismProperty (PointedSimplicialPresheaf.{w} C) :=
  MorphismProperty.monomorphisms _ ⊓ stalkwiseWeakEquivalences C J

/-- The object has the right lifting property against stalkwise trivial monomorphisms. -/
def IsStalkwiseInjectiveFibrant (X : PointedSimplicialPresheaf.{w} C) : Prop :=
  (stalkwiseTrivialMonomorphisms C J).rlp (toPoint C X)

variable [LocallySmall.{w} C]

/-- Smashing with a fixed pointed presheaf preserves the actual trivial monomorphisms. -/
theorem stalkwiseTrivialMonomorphisms_smashRightFunctor_map
    (Y : PointedSimplicialPresheaf.{w} C) {A B : PointedSimplicialPresheaf.{w} C} {i : A ⟶ B}
    (hi : stalkwiseTrivialMonomorphisms C J i) :
    stalkwiseTrivialMonomorphisms C J ((Under.smashRightFunctor Y).map i) := by
  let : Mono i := hi.1
  exact ⟨mono_smashRightFunctor_map Y i, stalkwiseWeakEquivalences_smashRightFunctor_map J Y hi.2⟩

/-- The pointed internal Hom preserves injective fibrancy for the stalkwise weak equivalences. -/
theorem isStalkwiseInjectiveFibrant_rightAdjoint_smash
    (Y : PointedSimplicialPresheaf.{w} C)
    {G : PointedSimplicialPresheaf.{w} C ⥤ PointedSimplicialPresheaf.{w} C}
    (adj : Under.smashRightFunctor Y ⊣ G) {X : PointedSimplicialPresheaf.{w} C}
    (hX : IsStalkwiseInjectiveFibrant C J X) :
    IsStalkwiseInjectiveFibrant C J (G.obj X) := by
  intro A B i hi
  let F := Under.smashRightFunctor Y
  have h : HasLiftingProperty i (G.map (toPoint C X)) :=
    (adj.hasLiftingProperty_iff i (toPoint C X)).1
      (hX (F.map i) (stalkwiseTrivialMonomorphisms_smashRightFunctor_map C J Y hi))
  let : G.IsRightAdjoint := adj.isRightAdjoint
  let t := (point_isZero.{w} C).isTerminal
  let e := (t.isTerminalObj G).uniqueUpToIso t
  have iso : Arrow.mk (G.map (toPoint C X)) ≅ Arrow.mk (toPoint C (G.obj X)) :=
    Arrow.isoMk (Iso.refl _) e (t.hom_ext _ _)
  exact (HasLiftingProperty.iff_of_arrow_iso_right i iso).1 h

end CategoryTheory.PointedSimplicialPresheaf
