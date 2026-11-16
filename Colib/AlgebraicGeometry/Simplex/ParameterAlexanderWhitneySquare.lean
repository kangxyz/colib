/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterAlexanderWhitneySummand
/-! # Alexander–Whitney and native presheaf parameter reindexing -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicTopology
open scoped Simplicial
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The genuine Alexander–Whitney map commutes with native parameter reindexing. -/
theorem parameterAlexanderWhitney_square (T : Sm)
    (M N : SimplicialObject (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) :
    alexanderWhitney (M ⋙ parameterReindex k T) (N ⋙ parameterReindex k T) ≫
      parameterAWTensorComparison k T M N =
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (parameterReindex k T)).app (M ⊗ N)).inv ≫
      ((parameterReindex k T).mapHomologicalComplex (.down ℕ)).map
        (alexanderWhitney M N) := by
  ext n : 1
  change awApp (M ⋙ parameterReindex k T) (N ⋙ parameterReindex k T) n ≫
      (parameterAWTensorComparison k T M N).f n =
    𝟙 _ ≫ (parameterReindex k T).map (awApp M N n)
  rw [Category.id_comp, awApp, awApp, Preadditive.sum_comp, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have h : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [awTerm_eq _ _ _ _ h (by omega) (by omega),
    awTerm_eq _ _ _ _ h (by omega) (by omega), Category.assoc,
    parameterAWTensorComparison_ι, Functor.map_comp]
  rfl

end AlgebraicSimplex
