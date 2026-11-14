/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChart

/-!
# Additivity of the original two-chart contraction

The actual induced cokernel map preserves sums of natural transformations. Consequently the
original contraction endofunctor is additive and preserves split exact sequences. Neither
additivity of the coefficient functors nor surjectivity of the chart difference is required.

Source: `Quillen/KTheory/Bass/TwoChartAdditive.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart

variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- Addition of coefficient transformations descends to addition of the original quotient maps. -/
@[simp]
theorem contractionMap_add {F G : D ⥤ AddCommGrpCat.{v}} (α β : F ⟶ G) :
    contractionMap p m (α + β) = contractionMap p m α + contractionMap p m β := by
  apply NatTrans.ext
  funext X
  apply contraction_hom_ext p m F X
  simp only [NatTrans.app_add, Preadditive.comp_add, contractionMap_π,
    Preadditive.add_comp]

/-- The original two-chart cokernel is an additive endofunctor on coefficient functors. -/
instance contractionFunctor_additive :
    (contractionFunctor p m : (D ⥤ AddCommGrpCat.{v}) ⥤ _).Additive where
  map_add := contractionMap_add p m _ _

end KTheory.Bass.TwoChart
