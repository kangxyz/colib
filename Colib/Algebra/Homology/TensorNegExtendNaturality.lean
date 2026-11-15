/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorNegExtendComponent
/-! # Naturality of the native chain-to-cochain tensor comparison -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace HomologicalComplex.TensorNegExtend
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- The original tensor extension comparison is natural in its two actual inputs. -/
theorem tensorNegExtendFullIso_naturality {K L K' L' : ChainComplex C ℕ}
    (a : K ⟶ K') (b : L ⟶ L') :
    HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
      (extendMap b ComplexShape.embeddingDownNat) ≫ (tensorNegExtendFullIso K' L').hom =
    (tensorNegExtendFullIso K L).hom ≫
      extendMap (HomologicalComplex.tensorHom a b) ComplexShape.embeddingDownNat := by
  ext i : 1
  by_cases hi : 0 < i
  · exact (isZero_tensorNegExtend_X K L i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  simp only [HomologicalComplex.comp_f]
  apply mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : 0 < p
  · exact ((tensorRight _).map_isZero
      (K.isZero_extend_X ComplexShape.embeddingDownNat p
        (by intro n; change -(n : ℤ) ≠ p; omega))).eq_of_src _ _
  by_cases hq : 0 < q
  · exact ((tensorLeft _).map_isZero
      (L.isZero_extend_X ComplexShape.embeddingDownNat q
        (by intro n; change -(n : ℤ) ≠ q; omega))).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ n : ℕ, q = -(n : ℤ) := ⟨(-q).toNat, by omega⟩
  have h : p + q = n := by change -(p : ℤ) + -(q : ℤ) = -(n : ℤ) at hpq; omega
  simp only [ι_mapBifunctorMap_assoc, tensorNegExtendFullIso_hom_ι K' L' p q n h,
    curriedTensor_map_app, curriedTensor_obj_map]
  erw [reassoc_of% tensorNegExtendFullIso_hom_ι K L p q n h]
  erw [extendMap_f a _ (i := p) rfl, extendMap_f b _ (i := q) rfl,
    extendMap_f (HomologicalComplex.tensorHom a b) _ (i := n) rfl]
  simp only [Iso.inv_hom_id_assoc, ι_mapBifunctorMap_assoc,
    curriedTensor_map_app, curriedTensor_obj_map]
  simp only [← tensorHom_def_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]
  simp only [negExtendIso, Iso.inv_hom_id, Category.comp_id]


end HomologicalComplex.TensorNegExtend
