/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic

/-! # Restricting the original sections in a signed lifting assertion

Only the original section is pulled back. The coefficient presheaf and the two
correction maps are unchanged.
-/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/RestrictionDifference/Restriction.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `f90487c5f339791df47a2ee2c8da46c847172bd6`. Original signs, coefficient actions and full
markings are retained. Geometric pencil production is not asserted here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

/-- A signed lift of every section also lifts restrictions of original sections.
This is restriction, not a surjectivity assertion on the new coefficient group. -/
theorem HasRestrictionDifferenceLifting.restrict
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O D D' T A : SmoothSite (Spec (.of k))}
    {φ : O ⟶ D} {β : O ⟶ A} {α : O ⟶ T}
    (h : P.HasRestrictionDifferenceLifting φ β α) (r : D ⟶ D') :
    P.HasRestrictionDifferenceLifting (φ ≫ r) β α := by
  intro d
  obtain ⟨a, c, hac⟩ := h (((toPresheaf k).obj P).map r.op d)
  refine ⟨a, c, ?_⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hac

/-- An actual isomorphism of the first correction source transports its section
contravariantly while keeping the original section and ambient correction. -/
theorem HasRestrictionDifferenceLifting.iso_right
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O D T A A' : SmoothSite (Spec (.of k))}
    {φ : O ⟶ D} {β : O ⟶ A} {α : O ⟶ T}
    (h : P.HasRestrictionDifferenceLifting φ β α) (e : A ≅ A') :
    P.HasRestrictionDifferenceLifting φ (β ≫ e.hom) α := by
  intro d
  let F := (toPresheaf k).obj P
  obtain ⟨a, c, hac⟩ := h d
  refine ⟨F.map e.inv.op a, c, ?_⟩
  change F.map (β ≫ e.hom).op (F.map e.inv.op a) - F.map α.op c = F.map φ.op d
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
    Category.assoc, e.hom_inv_id, Category.comp_id]
  exact hac

end AlgebraicGeometry.PresheafWithTransfers
