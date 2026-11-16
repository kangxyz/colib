/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartAdditive

/-!
# Additive iteration of the original two-chart contraction

The actual original cokernel functor can be iterated on any coefficient category, including
native scheme and under-ring rows. Every iterate is additive. Its maps retain the original
Laurent quotient equation at every step; no general preservation of exactness is asserted.

Source: `Quillen/KTheory/Bass/TwoChartIteration.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- Actual functorial iteration of the original two-chart cokernel. -/
def iteratedContractionFunctor : ℕ → (D ⥤ AddCommGrpCat.{v}) ⥤ (D ⥤ AddCommGrpCat.{v})
  | 0 => 𝟭 _
  | n + 1 => iteratedContractionFunctor n ⋙ contractionFunctor p m

/-- Every original iterate is additive and therefore preserves constructed split rows. -/
instance iteratedContractionFunctor_additive (n : ℕ) :
    (iteratedContractionFunctor p m n : (D ⥤ AddCommGrpCat.{v}) ⥤ _).Additive := by
  induction n with
  | zero => exact inferInstanceAs (Functor.Additive (𝟭 (D ⥤ AddCommGrpCat.{v})))
  | succ n ih =>
    let : (iteratedContractionFunctor p m n).Additive := ih
    exact inferInstanceAs
      (Functor.Additive (iteratedContractionFunctor p m n ⋙ contractionFunctor p m))

/-- The original Laurent projection square at each actual iteration. -/
@[reassoc]
theorem iteratedContractionFunctor_map_π {F G : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (n : ℕ) (X : D) :
    (contractionπ p m ((iteratedContractionFunctor p m n).obj F)).app X ≫
      ((iteratedContractionFunctor p m (n + 1)).map α).app X =
    ((iteratedContractionFunctor p m n).map α).app (L.obj X) ≫
      (contractionπ p m ((iteratedContractionFunctor p m n).obj G)).app X :=
  contractionMap_π p m ((iteratedContractionFunctor p m n).map α) X

end KTheory.Bass.TwoChart
