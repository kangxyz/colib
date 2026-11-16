/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap

/-! # The canonical projection map in terms of the unit and pushforward tensorator -/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal Functor.LaxMonoidal

namespace Colib.ProjectionMap

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.OplaxMonoidal] [G.LaxMonoidal]
  (adj : F ⊣ G) [adj.IsMonoidal]

/-- The actual adjunction-defined projection map is the unit followed by the actual
pushforward tensorator. This gives a sectionwise computation without changing the map. -/
theorem projectionMap_eq_unit_tensorator (K : C) (M : D) :
    adj.projectionMap K M = adj.unit.app K ▷ G.obj M ≫ μ G (F.obj K) M := by
  rw [Adjunction.projectionMap, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, Adjunction.unit_app_tensor_comp_map_δ,
    Category.assoc, ← Functor.LaxMonoidal.μ_natural_right]
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom]
  simp

end Colib.ProjectionMap
