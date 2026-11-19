/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # Inserting a genuine parameter section into the simplicial tensor

Pull back the first factor and pair it with a fixed section on the parameter.
The native singular parameter comparison supplies both naturality directions.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicTopology
open scoped TensorProduct Simplicial
universe u v w
namespace AlgebraicSimplex
variable (R : Type u) [CommRing R]
variable {K : Type w} [CommRing K]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of R))

/-- Pair the pulled-back first section with the parameter section. -/
def tensorParameterInsertion (P Q : (Smᵒᵖ ⥤ ModuleCat.{max v w} K))
    (T : Sm) (b : Q.obj (op T)) :
    P ⟶ (parameterReindex R T).obj (P ⊗ Q) where
  app U := ModuleCat.ofHom
    { toFun := fun s =>
        (P.map (SmoothSite.productFst U.unop T).op).hom s ⊗ₜ[K]
          (Q.map (SmoothSite.productSnd U.unop T).op).hom b
      map_add' := by intros; simp [TensorProduct.add_tmul]
      map_smul' := by intros; simp [TensorProduct.smul_tmul'] }
  naturality U V f := by
    ext s
    change (P.map (SmoothSite.productFst V.unop T).op).hom ((P.map f).hom s) ⊗ₜ[K]
      (Q.map (SmoothSite.productSnd V.unop T).op).hom b =
      TensorProduct.map (P.map (SmoothSite.productMap f.unop (𝟙 T)).op).hom
        (Q.map (SmoothSite.productMap f.unop (𝟙 T)).op).hom
        ((P.map (SmoothSite.productFst U.unop T).op).hom s ⊗ₜ[K]
          (Q.map (SmoothSite.productSnd U.unop T).op).hom b)
    rw [TensorProduct.map_tmul]
    congr 1
    · change (P.map f.unop.op ≫ P.map (SmoothSite.productFst V.unop T).op) s =
        (P.map (SmoothSite.productFst U.unop T).op ≫
          P.map (SmoothSite.productMap f.unop (𝟙 T)).op) s
      simp only [← P.map_comp, ← op_comp, SmoothSite.productMap_fst]
    · change (Q.map (SmoothSite.productSnd V.unop T).op) b =
        (Q.map (SmoothSite.productSnd U.unop T).op ≫
          Q.map (SmoothSite.productMap f.unop (𝟙 T)).op) b
      simp only [← Q.map_comp, ← op_comp, SmoothSite.productMap_snd, Category.comp_id]

/-- The parameter insertion is natural in every simplex operator. -/
def simplicialTensorParameterInsertion (P Q : (Smᵒᵖ ⥤ ModuleCat.{max v w} K))
    (T : Sm) (b : Q.obj (op T)) :
    simplicialPresheaf R P ⟶
      ((SimplicialObject.whiskering (Smᵒᵖ ⥤ ModuleCat.{max v w} K)
        (Smᵒᵖ ⥤ ModuleCat.{max v w} K)).obj (parameterReindex R T)).obj
        (simplicialPresheaf R (P ⊗ Q)) :=
  (simplicialPresheafFunctor R).map (tensorParameterInsertion R P Q T b) ≫
    (simplicialPresheafParameterIso R T (P ⊗ Q)).hom

/-- The actual alternating-face chain map, with no separate differential proof. -/
def chainTensorParameterInsertion (P Q : (Smᵒᵖ ⥤ ModuleCat.{max v w} K))
    (T : Sm) (b : Q.obj (op T)) :
    (singularChainsFunctor R).obj P ⟶
      ((parameterReindex R T).mapHomologicalComplex (.down ℕ)).obj
        ((singularChainsFunctor R).obj (P ⊗ Q)) :=
  singularChainsParameterMap R T (tensorParameterInsertion R P Q T b)

/-- The native chain insertion has the literal product-coordinate formula. -/
theorem chainTensorParameterInsertion_f_app
    (P Q : (Smᵒᵖ ⥤ ModuleCat.{max v w} K)) (T : Sm) (b : Q.obj (op T))
    (n : ℕ) (U : Sm)
    (s : P.obj (op (SmoothSite.product U (smoothSiteObj R n)))) :
    (((chainTensorParameterInsertion R P Q T b).f n).app (op U)).hom s =
      (P.map (SmoothSite.productMap (SmoothSite.productFst U T)
        (𝟙 (smoothSiteObj R n))).op).hom s ⊗ₜ[K]
      (Q.map (SmoothSite.productFst (SmoothSite.product U T) (smoothSiteObj R n) ≫
        SmoothSite.productSnd U T).op).hom b := by
  rw [chainTensorParameterInsertion, singularChainsParameterMap_f_app]
  change TensorProduct.map
      (P.map (SmoothSite.productSwapLast U T (smoothSiteObj R n)).op).hom
      (Q.map (SmoothSite.productSwapLast U T (smoothSiteObj R n)).op).hom
        ((P.map (SmoothSite.productFst (SmoothSite.product U (smoothSiteObj R n)) T).op).hom s
          ⊗ₜ[K]
        (Q.map (SmoothSite.productSnd (SmoothSite.product U (smoothSiteObj R n)) T).op).hom b) = _
  rw [TensorProduct.map_tmul]
  congr 1
  · change (P.map _ ≫ P.map _) s = _
    simp only [← P.map_comp, ← op_comp, SmoothSite.productSwapLast_fst]
  · change (Q.map _ ≫ Q.map _) b = _
    simp only [← Q.map_comp, ← op_comp, SmoothSite.productSwapLast_snd]
end AlgebraicSimplex
