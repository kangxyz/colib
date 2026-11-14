/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.ProjectionMapUnitTensorator
public import Colib.CategoryTheory.Monoidal.LeftAdjointUniqMonoidalOfUnit

/-! # Transporting the actual projection map along the canonical left-adjoint comparison -/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Functor.LaxMonoidal
namespace Colib.ProjectionMap
variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  {L H : C ⥤ D} {R : D ⥤ C}
  [L.Monoidal] [H.LaxMonoidal] [R.LaxMonoidal]
  (adjL : L ⊣ R) (adjH : H ⊣ R)
  [adjL.IsMonoidal] [NatTrans.IsMonoidal adjH.unit]

/-- The canonical native projection map, followed by the native tensorator, transforms
into the restriction unit/tensorator composite under the existing adjoint comparison. -/
theorem projectionMap_leftAdjointUniq (A B : C) :
    adjL.projectionMap A (L.obj B) ≫ R.map (μ L A B) ≫
        R.map ((adjL.leftAdjointUniq adjH).hom.app (A ⊗ B)) =
      (A ◁ R.map ((adjL.leftAdjointUniq adjH).hom.app B)) ≫
        adjH.unit.app A ▷ R.obj (H.obj B) ≫
        μ R (H.obj A) (H.obj B) ≫ R.map (μ H A B) := by
  have := Colib.MonoidalAdjunction.leftAdjointUniq_isMonoidal_of_unit adjL adjH
  rw [projectionMap_eq_unit_tensorator]
  simp only [← Functor.map_comp, ← Category.assoc]
  rw [NatTrans.IsMonoidal.tensor]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← μ_natural_assoc]
  -- The remaining square is tensor bifunctoriality and the existing unit comparison.
  simp only [← Category.assoc, ← tensorHom_id, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [Adjunction.unit_leftAdjointUniq_hom_app]

end Colib.ProjectionMap
