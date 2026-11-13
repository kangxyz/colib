/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.Homotopy
public import Colib.Topology.HELP.StrictLift

/-!
# Descent of strict compact lifting problems through filtered realizations

Compact source maps, equality on the boundary, and homotopies relative to
that boundary descend through the original filtered simplicial diagrams.
The same statements apply to the neighborhood diagrams of site points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology

universe u v w

namespace Topology.FilteredRealization

variable {J : Type u} [SmallCategory J]
  {F G : J ⥤ SSet.{u}} (η : F ⟶ G) (c : Cocone F) (d : Cocone G)
  (f : c.pt ⟶ d.pt) (hf : ∀ j, c.ι.app j ≫ f = η.app j ≫ d.ι.app j)
  {A : Type v} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]

include hf in
private theorem realization_cocone_naturality (j : J) :
    (SSet.toTop.map f).hom.comp (SSet.toTop.map (c.ι.app j)).hom =
      (SSet.toTop.map (d.ι.app j)).hom.comp (SSet.toTop.map (η.app j)).hom := by
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, hf]

private theorem realization_stage_naturality {j k : J} (p : j ⟶ k) :
    (SSet.toTop.map (G.map p)).hom.comp (SSet.toTop.map (η.app j)).hom =
      (SSet.toTop.map (η.app k)).hom.comp (SSet.toTop.map (F.map p)).hom := by
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp,
    η.naturality]

private theorem realization_cocone_comp {D : J ⥤ SSet.{u}} (e : Cocone D)
    {j k : J} (p : j ⟶ k) :
    (SSet.toTop.map (e.ι.app k)).hom.comp (SSet.toTop.map (D.map p)).hom =
      (SSet.toTop.map (e.ι.app j)).hom := by
  rw [← TopCat.hom_comp, ← Functor.map_comp, e.w]

variable [IsFiltered J]

include hf in
/-- A strict compact square into the colimit, with its source already at
one stage, has a strict representative above that stage. -/
theorem compact_strictSquare_factors [CompactSpace A] [CompactSpace B]
    (hd : IsColimit d) (j : J) (i : C(A, B)) (a : C(A, |F.obj j|)) (b : C(B, |d.pt|))
    (h : (SSet.toTop.map f).hom.comp ((SSet.toTop.map (c.ι.app j)).hom.comp a) = b.comp i) :
    ∃ (k : J) (p : j ⟶ k) (b' : C(B, |G.obj k|)),
      (SSet.toTop.map (d.ι.app k)).hom.comp b' = b ∧
        (SSet.toTop.map (η.app k)).hom.comp ((SSet.toTop.map (F.map p)).hom.comp a) =
          b'.comp i := by
  obtain ⟨k, p, b₀, hb₀⟩ := compact_factors_above G d hd j b
  let a₀ := (SSet.toTop.map (F.map p)).hom.comp a
  have h₀ : (SSet.toTop.map (c.ι.app k)).hom.comp a₀ =
      (SSet.toTop.map (c.ι.app j)).hom.comp a := by
    dsimp only [a₀]
    rw [← ContinuousMap.comp_assoc, realization_cocone_comp]
  have e : (SSet.toTop.map (d.ι.app k)).hom.comp ((SSet.toTop.map (η.app k)).hom.comp a₀) =
      (SSet.toTop.map (d.ι.app k)).hom.comp (b₀.comp i) := by
    rw [← ContinuousMap.comp_assoc, ← realization_cocone_naturality η c d f hf,
      ContinuousMap.comp_assoc, h₀, h, ← ContinuousMap.comp_assoc, hb₀]
  obtain ⟨l, q, eq⟩ := compact_eq_eventually G d hd k _ _ e
  refine ⟨l, p ≫ q, (SSet.toTop.map (G.map q)).hom.comp b₀, ?_, ?_⟩
  · rw [← ContinuousMap.comp_assoc, realization_cocone_comp, hb₀]
  · calc
      _ = (SSet.toTop.map (G.map q)).hom.comp ((SSet.toTop.map (η.app k)).hom.comp a₀) := by
        ext x
        change SSet.toTop.map (η.app l) (SSet.toTop.map (F.map (p ≫ q)) (a x)) =
          SSet.toTop.map (G.map q) (SSet.toTop.map (η.app k) (SSet.toTop.map (F.map p) (a x)))
        rw [F.map_comp, Functor.map_comp]
        exact (ContinuousMap.congr_fun (realization_stage_naturality η q)
          (SSet.toTop.map (F.map p) (a x))).symm
      _ = (SSet.toTop.map (G.map q)).hom.comp (b₀.comp i) := eq
      _ = _ := (ContinuousMap.comp_assoc _ _ _).symm

include hf in
/-- A strict compact lift and its relative homotopy in the colimit are
witnessed at one later stage with the exact original boundary values. -/
theorem compact_strictLift_eventually [CompactSpace A] [CompactSpace B]
    (hc : IsColimit c) (hd : IsColimit d) (j : J)
    (i : C(A, B)) (a : C(A, |F.obj j|)) (b : C(B, |G.obj j|))
    (h : StrictHomotopyLift (SSet.toTop.map f).hom i
      ((SSet.toTop.map (c.ι.app j)).hom.comp a) ((SSet.toTop.map (d.ι.app j)).hom.comp b)) :
    ∃ (k : J) (p : j ⟶ k), StrictHomotopyLift (SSet.toTop.map (η.app k)).hom i
      ((SSet.toTop.map (F.map p)).hom.comp a) ((SSet.toTop.map (G.map p)).hom.comp b) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := h
  obtain ⟨k, p, r₀, hr₀⟩ := compact_factors_above F c hc j r
  have e : (SSet.toTop.map (c.ι.app k)).hom.comp (r₀.comp i) =
      (SSet.toTop.map (c.ι.app k)).hom.comp ((SSet.toTop.map (F.map p)).hom.comp a) := by
    rw [← ContinuousMap.comp_assoc, hr₀, hr]
    rw [← ContinuousMap.comp_assoc, realization_cocone_comp]
  obtain ⟨l, q, eq⟩ := compact_eq_eventually F c hc k _ _ e
  let r₁ := (SSet.toTop.map (F.map q)).hom.comp r₀
  let b₁ := (SSet.toTop.map (G.map (p ≫ q))).hom.comp b
  have hr₁ : (SSet.toTop.map (c.ι.app l)).hom.comp r₁ = r := by
    dsimp only [r₁]
    rw [← ContinuousMap.comp_assoc, realization_cocone_comp, hr₀]
  have hri : r₁.comp i = (SSet.toTop.map (F.map (p ≫ q))).hom.comp a := by
    dsimp only [r₁]
    rw [ContinuousMap.comp_assoc, eq, ← ContinuousMap.comp_assoc,
      ← TopCat.hom_comp, ← Functor.map_comp, ← F.map_comp]
  have h₀ : (SSet.toTop.map (d.ι.app l)).hom.comp ((SSet.toTop.map (η.app l)).hom.comp r₁) =
      (SSet.toTop.map f).hom.comp r := by
    rw [← ContinuousMap.comp_assoc, ← realization_cocone_naturality η c d f hf,
      ContinuousMap.comp_assoc, hr₁]
  have h₁ : (SSet.toTop.map (d.ι.app l)).hom.comp b₁ =
      (SSet.toTop.map (d.ι.app j)).hom.comp b := by
    dsimp only [b₁]
    rw [← ContinuousMap.comp_assoc, realization_cocone_comp]
  obtain ⟨m, s, ⟨K⟩⟩ := homotopyRel_factors G d hd l (Set.range i)
    (isCompact_range i.continuous) (H.cast h₀.symm h₁.symm)
  refine ⟨m, (p ≫ q) ≫ s, (SSet.toTop.map (F.map s)).hom.comp r₁, ?_, ⟨K.cast ?_ ?_⟩⟩
  · rw [ContinuousMap.comp_assoc, hri, ← ContinuousMap.comp_assoc,
      ← TopCat.hom_comp, ← Functor.map_comp, ← F.map_comp]
  · rw [← ContinuousMap.comp_assoc, realization_stage_naturality η, ContinuousMap.comp_assoc]
  · dsimp only [b₁]
    rw [← ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← Functor.map_comp, ← G.map_comp]

end Topology.FilteredRealization
