/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.TwoChart

/-!
# Pointwise epimorphisms of the original Bass quotient map

The original induced cokernel map is epimorphic at an object as soon as the
input transformation is epimorphic at its Laurent object. Two contractions
need only the double Laurent component. No source-category additivity or
polynomial-chart epimorphism is required.

Adapted from the original construction in `Quillen/KTheory/Bass/TwoChartMapEpi.lean`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- Surjectivity at the actual Laurent object suffices for the original quotient map. -/
theorem epi_contractionMap_app {F G : D ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (X : D)
    [Epi (α.app (L.obj X))] : Epi ((contractionMap p m α).app X) :=
  epi_of_epi_fac (contractionMap_π p m α X)

/-- The twice-induced quotient map needs only the actual double Laurent component. -/
theorem epi_doubleContractionMap_app {F G : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (X : D) [Epi (α.app (L.obj (L.obj X)))] :
    Epi ((contractionMap p m (contractionMap p m α)).app X) := by
  have := epi_contractionMap_app p m α (L.obj X)
  exact epi_contractionMap_app p m (contractionMap p m α) X

end KTheory.Bass.TwoChart
