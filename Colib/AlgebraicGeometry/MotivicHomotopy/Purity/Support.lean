/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.CategoryTheory.Triangulated.Stabilization.Stages

/-! # The original effective motives with support and their Lefschetz twists -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open SmoothSite

set_option backward.defeqAttrib.useBackward true

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable {k : Type u} [Field k]

variable {Z Z' Z'' X X' X'' : SmoothSite (Spec (CommRingCat.of k))}
  {i : Z ⟶ X} {j : Z' ⟶ X'} {l : Z'' ⟶ X''}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] [IsClosedImmersion l.left]

/-- The original map of complementary opens and ambient schemes. -/
def closedSupportArrowMap {f : X ⟶ X'} {g : Z ⟶ Z'}
    (_h : IsPullback i.left g.left f.left j.left) :
    Arrow.mk (closedPairOpenInclusion i.left) ⟶ Arrow.mk (closedPairOpenInclusion j.left) := by
  let a : ((opensFunctor X).obj (closedPairOpen i.left)) ⟶ X :=
    closedPairOpenInclusion i.left
  let b : ((opensFunctor X').obj (closedPairOpen j.left)) ⟶ X' :=
    closedPairOpenInclusion j.left
  let c : (opensFunctor X).obj (closedPairOpen i.left) ⟶
      (opensFunctor X').obj (closedPairOpen j.left) := closedPairOpenMap _h
  have hc : c ≫ b = a ≫ f := closedPairOpenMap_comm _h
  exact Arrow.homMk' c f hc

/-- A map of open pairs is determined by its ambient component. -/
theorem openPairArrowMap_eq_of_right {U U' : SmoothSite (Spec (CommRingCat.of k))}
    {f : U ⟶ X} {f' : U' ⟶ X'}
    [IsOpenImmersion f'.left]
    {a b : Arrow.mk f ⟶ Arrow.mk f'}
    (h : a.right = b.right) : a = b := by
  let : Mono f' := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono f'.left))
  apply Arrow.hom_ext
  · apply (cancel_mono f').mp
    exact (Arrow.w a).trans
      ((congrArg (fun u => f ≫ u) h).trans (Arrow.w b).symm)
  · exact h

/-- The original open-complement map is determined by its ambient map. -/
theorem closedSupportArrowMap_eq_of_right
    {a b : Arrow.mk (closedPairOpenInclusion i.left) ⟶
      Arrow.mk (closedPairOpenInclusion j.left)}
    (h : a.right = b.right) : a = b :=
  openPairArrowMap_eq_of_right h

/-- Open-complement maps compose according to the ambient composition. -/
theorem closedSupportArrowMap_comp {f : X ⟶ X'} {g : Z ⟶ Z'}
    {f' : X' ⟶ X''} {g' : Z' ⟶ Z''}
    (h : IsPullback i.left g.left f.left j.left)
    (h' : IsPullback j.left g'.left f'.left l.left) :
    closedSupportArrowMap h ≫ closedSupportArrowMap h' =
      closedSupportArrowMap (f := f ≫ f') (g := g ≫ g') (h.paste_vert h') :=
  closedSupportArrowMap_eq_of_right rfl

/-- The isomorphism of supported motives identifies the original open
complements through the given ambient isomorphism. -/
def closedSupportArrowIso (e : X ≅ X') (d : Z ≅ Z')
    (h : i ≫ e.hom = d.hom ≫ j) :
    Arrow.mk (closedPairOpenInclusion i.left) ≅ Arrow.mk (closedPairOpenInclusion j.left) := by
  let h₁ : IsPullback i.left d.hom.left e.hom.left j.left :=
    IsPullback.of_vert_isIso ⟨congrArg (fun a => a.left) h⟩
  have h' : j ≫ e.inv = d.inv ≫ i := by
    calc
      j ≫ e.inv = d.inv ≫ (d.hom ≫ j) ≫ e.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = d.inv ≫ i := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let h₂ : IsPullback j.left d.inv.left e.inv.left i.left :=
    IsPullback.of_vert_isIso ⟨congrArg (fun a => a.left) h'⟩
  let a := closedSupportArrowMap h₁
  let b := closedSupportArrowMap h₂
  exact
    { hom := a
      inv := b
      hom_inv_id := closedSupportArrowMap_eq_of_right e.hom_inv_id
      inv_hom_id := closedSupportArrowMap_eq_of_right e.inv_hom_id }

@[simp]
theorem closedSupportArrowIso_hom_right (e : X ≅ X') (d : Z ≅ Z')
    (h : i ≫ e.hom = d.hom ≫ j) :
    (closedSupportArrowIso e d h).hom.right = e.hom := rfl

@[simp]
theorem closedSupportArrowIso_inv_right (e : X ≅ X') (d : Z ≅ Z')
    (h : i ≫ e.hom = d.hom ≫ j) :
    (closedSupportArrowIso e d h).inv.right = e.inv := rfl

section Motives

variable (k) [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original relative motive of the complement of the indicated closed support. -/
abbrev effectiveMotiveWithSupport {Z X : SmoothSite (Spec (.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i.left] :=
  effectivePairMotive k (closedPairOpenInclusion i.left)

/-- Maps of actual relative motives are induced by the original inclusions. -/
abbrev effectiveMotiveWithSupportMap {f : X ⟶ X'} {g : Z ⟶ Z'}
    (h : IsPullback i.left g.left f.left j.left) :
    effectiveMotiveWithSupport k i ⟶ effectiveMotiveWithSupport k j :=
  (effectivePairMotiveFunctor k).map (closedSupportArrowMap h)

/-- An isomorphism of closed supports gives the original isomorphism of relative motives. -/
def effectiveMotiveWithSupportIso (e : X ≅ X') (d : Z ≅ Z')
    (h : i ≫ e.hom = d.hom ≫ j) :
    effectiveMotiveWithSupport k i ≅ effectiveMotiveWithSupport k j :=
  (effectivePairMotiveFunctor k).mapIso (closedSupportArrowIso e d h)

end Motives

end AlgebraicGeometry.MotivicHomotopy
