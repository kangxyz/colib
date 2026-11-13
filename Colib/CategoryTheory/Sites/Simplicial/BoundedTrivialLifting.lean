/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedIntersection
public import Colib.CategoryTheory.Sites.Simplicial.BoundedTrivialGenerators
public import Colib.CategoryTheory.Sites.Simplicial.PartialLifts
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Lifting against the bounded stalkwise trivial generators

A right lift against the small chosen family extends along every
stalkwise trivial monomorphism. The extension through intermediate
subpresheaves preserves the original basepoint because it agrees on the
original source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite SimplicialSubpresheaf

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

/-- A lift of the underlying square preserves the original basepoint. -/
theorem hasLiftingProperty_of_right {X Y Z T : PointedSimplicialPresheaf.{max u v} C}
    (i : X ⟶ Y) (p : Z ⟶ T) (h : HasLiftingProperty i.right p.right) :
    HasLiftingProperty i p := by
  constructor
  intro a b sq
  let q : CommSq a.right i.right p.right b.right :=
    ⟨congrArg (fun f => f.right) sq.w⟩
  let : HasLiftingProperty i.right p.right := h
  let l := q.lift
  have hl : Y.hom ≫ l = Z.hom := by
    rw [← Under.w i, Category.assoc, q.fac_left, Under.w]
  refine ⟨⟨{ l := Under.homMk l hl, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply Under.UnderMorphism.ext
    exact q.fac_left
  · apply Under.UnderMorphism.ext
    exact q.fac_right

private def isoRange {P Q : Cᵒᵖ ⥤ SSet.{max u v}} (i : P ⟶ Q) [Mono i] :
    P ≅ toPresheaf (Subfunctor.range (Functor.uncurry.map i)) := by
  let E : (Cᵒᵖ ⥤ SSet.{max u v}) ≌ ((Cᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type (max u v)) := Functor.currying
  let : Mono (E.functor.map i) := E.functor.map_mono i
  exact (E.unitIso.app P) ≪≫ E.inverse.mapIso (asIso (Subfunctor.toRange (E.functor.map i)))

private theorem isoRange_hom_inclusion {P Q : Cᵒᵖ ⥤ SSet.{max u v}} (i : P ⟶ Q) [Mono i] :
    (isoRange C i).hom ≫ inclusion (Subfunctor.range (Functor.uncurry.map i)) = i := by
  let A := Subfunctor.range (Functor.uncurry.map i)
  change lift i (A := A) (le_rfl : A ≤ A) ≫ inclusion A = i
  exact lift_inclusion i le_rfl

/-- The literal range inclusion has the same left lifting property as the mono. -/
theorem hasLiftingProperty_inclusion_range {P Q X Y : Cᵒᵖ ⥤ SSet.{max u v}}
    (i : P ⟶ Q) [Mono i] (p : X ⟶ Y)
    (h : HasLiftingProperty (inclusion (Subfunctor.range (Functor.uncurry.map i))) p) :
    HasLiftingProperty i p := by
  let A := Subfunctor.range (Functor.uncurry.map i)
  let e : P ≅ toPresheaf A := isoRange C i
  have he : e.hom ≫ inclusion A = i := isoRange_hom_inclusion C i
  let j : Arrow.mk i ≅ Arrow.mk (inclusion A) := Arrow.isoMk' i (inclusion A) e (Iso.refl Q) (by
    simpa only [Iso.refl_hom, Category.comp_id] using he)
  exact (HasLiftingProperty.iff_of_arrow_iso_left j p).2 h

/-- The right lifting property against the freely pointed bounded maps
is the right lifting property against every actual stalkwise trivial
monomorphism. -/
theorem rlp_boundedTrivialGenerators_eq
    {F : ObjectProperty (J.Point.{max u v})} [ObjectProperty.Small.{max u v} F]
    (hF : F.IsConservativeFamilyOfPoints)
    (κ : Cardinal.{max u v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hFκ : HasCardinalLT F.FullSubcategory κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ)
    (hPoint : ∀ ψ : F.FullSubcategory, ∀ U : C, HasCardinalLT (ψ.obj.fiber.obj U) κ) :
    (boundedTrivialGenerators C J κ).rlp = (stalkwiseTrivialMonomorphisms C J).rlp := by
  apply le_antisymm ?_ (MorphismProperty.antitone_rlp (boundedTrivialGenerators_le C J κ))
  intro X Y p hp P Q i hi
  let : Mono i := hi.1
  let : Mono i.right := Under.mono_right_of_mono i
  apply hasLiftingProperty_of_right C
  apply hasLiftingProperty_inclusion_range C i.right p.right
  let A := Subfunctor.range (Functor.uncurry.map i.right)
  let e : P.right ≅ toPresheaf A := isoRange C i.right
  have he : e.hom ≫ inclusion A = i.right := isoRange_hom_inclusion C i.right
  have hA (Φ : J.Point.{max u v}) :
      SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (inclusion A)) := by
    let E := Φ.presheafFiber (A := SSet.{max u v})
    have h : SSet.IsRealizationWeakEquivalence (E.map (e.hom ≫ inclusion A)) := by
      rw [he]
      exact hi.2 Φ
    rw [Functor.map_comp] at h
    exact h.of_comp_left (SSet.IsRealizationWeakEquivalence.of_isIso (E.map e.hom))
  refine hasLiftingProperty_inclusion_of_extend (J := J) hA ?_
  intro B hB q s
  obtain ⟨D, hs, hD, hw⟩ := exists_bounded_weak_intersection hF B hB κ hκ hFκ hC hPoint s
  let hBDle : B ⊓ D ≤ D := inf_le_right
  let j : toPresheaf (B ⊓ D) ⟶ toPresheaf D := SimplicialSubpresheaf.homOfLE hBDle
  let : Mono j := mono_of_mono_fac (homOfLE_inclusion hBDle)
  have hBD : HasBoundedSections (B ⊓ D) κ :=
    hasBoundedSections_of_le (inf_le_right : B ⊓ D ≤ D) hD
  obtain ⟨_, _, g, hg, ⟨e⟩⟩ := isoClosure_boundedTrivialGenerators C J κ j hw hBD hD
  have hl := (HasLiftingProperty.iff_of_arrow_iso_left e p).1 (hp g hg)
  exact ⟨D, hs, hw, (freeForgetAdjunction C).hasLiftingProperty_iff j p |>.1 hl⟩

end CategoryTheory.PointedSimplicialPresheaf
