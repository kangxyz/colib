/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateAWSource
/-! # The exact surviving summand after constant augmentation -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory
open scoped Simplicial
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- Augmentation, not the original constant chain, kills every summand with positive
second degree. The surviving map is the genuine `(n,0)` inclusion. -/
theorem constantCoordinateAWSourceIso_hom_f (M : SimplicialObject C) (A : C) (n : ℕ) :
    (constantCoordinateAWSourceIso M A).hom.f n =
      HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj M)
        ((ChainComplex.single₀ C).obj A) n 0 n (add_zero n) := by
  change awApp M ((SimplicialObject.const C).obj A) n ≫
    (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
      (constAugmentationEquiv A).hom).f n = _
  rw [awApp, Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem (n, 0)
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero n)) ?_]
  · rw [awTerm_eq _ _ _ _ (add_zero n) (by omega) (by omega),
      Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [subinterval_zero_self, op_id, M.map_id, Functor.const_obj_map,
      HomologicalComplex.id_f, curriedTensor_map_app,
      constAugmentationEquiv_hom_f_zero, id_whiskerRight]
    erw [id_tensorHom_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp]
  · rintro ⟨p, q⟩ hx hne
    have h : p + q = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact absurd (Prod.ext (by omega) h0) hne
      · exact ⟨q - 1, by omega⟩
    rw [awTerm_eq _ _ _ _ h (by omega) (by omega),
      Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      alternatingFaceMapComplex_obj_X, id_whiskerRight, curriedTensor_obj_obj,
      constAugmentationEquiv_hom_f_succ, MonoidalPreadditive.whiskerLeft_zero,
      comp_zero, zero_comp]

end AlgebraicTopology
