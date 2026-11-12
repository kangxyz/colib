/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Surjectivity on the literal stage-boundary pullbacks -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Preserve the actual stage-boundary object when transporting a full-boundary
surjectivity result through F and kappa. Both comparisons are actual pullback squares. -/
theorem surjective_actual_stage_boundary_pullbacks
    {C U Z D Cnew V A : Scheme.{u}}
    (r : C ⟶ U) (d : Z ⟶ U) (b : D ⟶ C) (t : D ⟶ Z)
    (hb : IsPullback b t r d) (F : Cnew ⟶ C) (κ : V ⟶ Cnew) (q : Cnew ⟶ A)
    [Surjective (pullback.fst κ (pullback.fst (F ≫ r) d) ≫ κ ≫ q)] :
    Surjective (pullback.fst κ (pullback.fst F b) ≫ κ ≫ q) := by
  let hnew := (IsPullback.of_hasPullback F b).paste_vert hb
  let hactual := (IsPullback.of_hasPullback κ (pullback.fst F b)).paste_vert hnew
  let hcanonical := (IsPullback.of_hasPullback κ (pullback.fst (F ≫ r) d)).paste_vert
    (IsPullback.of_hasPullback (F ≫ r) d)
  let e := hactual.isoPullback ≪≫ hcanonical.isoPullback.symm
  have he : e.hom ≫ pullback.fst κ (pullback.fst (F ≫ r) d) =
      pullback.fst κ (pullback.fst F b) := by
    change (hactual.isoPullback.hom ≫ hcanonical.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, hcanonical.isoPullback_inv_fst, hactual.isoPullback_hom_fst]
  have H : Surjective (e.hom ≫ (pullback.fst κ (pullback.fst (F ≫ r) d) ≫ κ ≫ q)) :=
    inferInstance
  simpa only [← Category.assoc, he] using H

end AlgebraicGeometry.Scheme
