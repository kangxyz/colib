/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterAlexanderWhitney
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

/-- On each native total-tensor summand the comparison is literal reindexing. -/
theorem parameterAWTensorComparison_ι (T : Sm)
    (M N : SimplicialObject (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ))
    (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        ((alternatingFaceMapComplex _).obj (M ⋙ parameterReindex k T))
        ((alternatingFaceMapComplex _).obj (N ⋙ parameterReindex k T)) p q n h ≫
      (parameterAWTensorComparison k T M N).f n =
    (parameterReindex k T).map (HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex _).obj M)
      ((alternatingFaceMapComplex _).obj N) p q n h) := by
  simp only [parameterAWTensorComparison, HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Iso.app_inv,
    alternatingFaceMapComplexCompMapHomologicalComplexIso_inv_app_f,
    curriedTensor_map_app, curriedTensor_obj_map]
  erw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.id_comp]
  have ht := Functor.ι_mapHomologicalComplexTensorator_hom (parameterReindex k T)
    ((alternatingFaceMapComplex _).obj M) ((alternatingFaceMapComplex _).obj N) p q n h
  have hμ : Functor.LaxMonoidal.μ (parameterReindex k T)
      (((alternatingFaceMapComplex _).obj M).X p)
      (((alternatingFaceMapComplex _).obj N).X q) = 𝟙 _ := rfl
  rw [hμ, Category.id_comp] at ht
  exact ht

end AlgebraicSimplex
