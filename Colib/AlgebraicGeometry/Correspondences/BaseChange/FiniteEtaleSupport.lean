/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteEtalePullback
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-! # Finite-correspondence support under finite étale pullback

In a Cartesian square over a finite flat map of source schemes, an ambient
point is admissible exactly when its image is admissible. The reduced
closures are finite over their respective sources and their projected points
are generic in the corresponding source components. This permits the
coefficientwise étale descent of native cycles to retain finite-correspondence
support in Riou, *Opérations de Steenrod motiviques*, Definition 2.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Chow

variable {S T X X' Y Y' : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ T} {g' : Y' ⟶ T}

private theorem range_integralComponentAt_comp_eq_closure {A B : Scheme.{u}}
    (p : A ⟶ B) (z : A) (hfin : IsFinite ((integralComponentAt z).subschemeι ≫ p)) :
    Set.range ((integralComponentAt z).subschemeι ≫ p) = closure ({p z} : Set B) := by
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let q := (integralComponentAt z).subschemeι ≫ p
  have : IsFinite q := hfin
  have hclosed : IsClosed (Set.range q) := by
    rw [← Set.image_univ]
    exact q.isClosedMap _ isClosed_univ
  have hgen := (genericPoint_spec (integralComponentAt z).subscheme).image q.continuous
  rw [Set.image_univ, hclosed.closure_eq, IsGenericPoint] at hgen
  have hpoint : (integralComponentAt z).subschemeι
      (genericPoint (integralComponentAt z).subscheme) = z :=
    genericPointOf_integralComponentAt z
  simpa only [q, Scheme.Hom.comp_apply, hpoint] using hgen.symm

section

variable [IsSeparated g] [LocallyOfFiniteType g]
  {a : X' ⟶ X} [IsFinite a] [Flat a] {b : pullback f' g' ⟶ pullback f g}
  (sq : IsPullback b (pullback.fst f' g') (pullback.fst f g) a)

include sq in
set_option backward.isDefEq.respectTransparency false in
/-- Finite flat pullback preserves and reflects admissibility of each support point. -/
theorem isFiniteCorrespondencePoint_iff_of_isPullback_of_finiteFlat
    (z : (pullback f' g' : Scheme.{u})) :
    IsFiniteCorrespondencePoint f' g' z ↔ IsFiniteCorrespondencePoint f g (b z) := by
  have hb : IsFinite b := MorphismProperty.of_isPullback sq.flip (inferInstance : IsFinite a)
  have hz : pullback.fst f g (b z) = a (pullback.fst f' g' z) :=
    congrArg (fun m : (pullback f' g' : Scheme.{u}) ⟶ X ↦ m z) sq.w
  constructor
  · rintro ⟨hfin, hcomp⟩
    have hfin' : IsFinite (((integralComponentAt z).subschemeι ≫ b) ≫ pullback.fst f g) := by
      rw [Category.assoc, sq.w, ← Category.assoc]
      infer_instance
    have hfin'' := finiteCyclePushforward_isFinite_integralComponentAt b
      (pullback.fst f g) z hfin'
    refine ⟨hfin'', ?_⟩
    rw [range_integralComponentAt_comp_eq_closure _ _ hfin'']
    rw [range_integralComponentAt_comp_eq_closure _ _ hfin] at hcomp
    rw [hz]
    exact mem_genericPoints_of_flat a hcomp
  · rintro ⟨hfin, hcomp⟩
    let W := integralComponentAt (b z)
    have hW : IsFinite ((W.comap b).subschemeι ≫ pullback.fst f' g') :=
      MorphismProperty.of_isPullback ((isPullback_comapRestrict W b).flip.paste_vert sq) hfin
    have hle : W.comap b ≤ integralComponentAt z := by
      apply le_support_iff_le_vanishingIdeal.mp
      rw [TopologicalSpace.Closeds.closure_le, support_comap]
      exact Set.singleton_subset_iff.mpr (by
        change b z ∈ (W.support : Set (pullback f g : Scheme.{u}))
        rw [coe_support_integralComponentAt]
        exact subset_closure (Set.mem_singleton _))
    have hfin' : IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst f' g') := by
      rw [← inclusion_subschemeι hle, Category.assoc]
      infer_instance
    refine ⟨hfin', ?_⟩
    rw [range_integralComponentAt_comp_eq_closure _ _ hfin']
    apply mem_genericPoints_of_isFinite_image a
    rw [← hz]
    rwa [range_integralComponentAt_comp_eq_closure _ _ hfin] at hcomp

/-- Coefficientwise étale pullback takes native finite correspondences to native
finite correspondences in the Cartesian ambient product. -/
def finiteCorrespondencesEtalePullback [IsFinite b] [Etale b] :
    finiteCorrespondences f g →+ finiteCorrespondences f' g' where
  toFun c := ⟨finiteEtaleCyclePullback b c.val,
    ⟨finiteEtaleCyclePullback_finite_support b c.val c.property.1,
      fun z hz ↦ (isFiniteCorrespondencePoint_iff_of_isPullback_of_finiteFlat sq z).mpr
        (c.property.2 (b z) hz)⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)

@[simp]
theorem finiteCorrespondencesEtalePullback_apply [IsFinite b] [Etale b]
    (c : finiteCorrespondences f g) (z : (pullback f' g' : Scheme.{u})) :
    (finiteCorrespondencesEtalePullback sq c).val z = c.val (b z) := rfl

/-- Descent of a finite correspondence is equivalent to equality of the two
actual ambient cycle pullbacks over the cover. -/
theorem existsUnique_finiteCorrespondencesEtalePullback [IsFinite b] [Etale b]
    [Surjective a] (c : finiteCorrespondences f' g') :
    (∃! d : finiteCorrespondences f g, finiteCorrespondencesEtalePullback sq d = c) ↔
      finiteEtaleCyclePullback (pullback.fst b b) c.val =
        finiteEtaleCyclePullback (pullback.snd b b) c.val := by
  have : Surjective b := MorphismProperty.of_isPullback sq.flip (inferInstance : Surjective a)
  constructor
  · rintro ⟨d, hd, -⟩
    apply (existsUnique_finiteEtaleCyclePullback b b.surjective c.val c.property.1).mp
    refine ⟨d.val, ⟨d.property.1, congrArg Subtype.val hd⟩, fun d' hd' ↦ ?_⟩
    exact finiteEtaleCyclePullback_injective b b.surjective
      (hd'.2.trans (congrArg Subtype.val hd).symm)
  · intro h
    obtain ⟨d, ⟨hfin, hd⟩, -⟩ :=
      (existsUnique_finiteEtaleCyclePullback b b.surjective c.val c.property.1).mpr h
    have hsupport (y : (pullback f g : Scheme.{u})) (hy : d y ≠ 0) :
        IsFiniteCorrespondencePoint f g y := by
      obtain ⟨z, rfl⟩ := b.surjective y
      apply (isFiniteCorrespondencePoint_iff_of_isPullback_of_finiteFlat sq z).mp
      apply c.property.2 z
      rw [← hd, finiteEtaleCyclePullback_apply]
      exact hy
    refine ⟨⟨d, hfin, hsupport⟩, Subtype.ext hd, fun d' hd' ↦ Subtype.ext ?_⟩
    exact finiteEtaleCyclePullback_injective b b.surjective
      ((congrArg Subtype.val hd').trans hd.symm)

end

end Stacks.Chow
