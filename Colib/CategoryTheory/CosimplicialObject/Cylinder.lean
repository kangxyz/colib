/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.SimplexCategory.Prism
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# The actual categorical cylinder of a cosimplicial object

The cylinder in degree `n` is the categorical product of the interval and the
original simplex. Its prism maps use Mathlib's canonical `toMk₁` and the actual
cosimplicial degeneracies. Pullback by any presheaf gives a simplicial homotopy
of the two endpoint restrictions. This is independent of any coefficient
contraction or homotopy-invariance hypothesis.

Adapted from `SingularComplex/Endpoints.lean` in `kangxyz/motivic` at
a6805c4a87cdfd7717dd7a94039246a167f15380, using the existing Colib prism identities
instead of the source's separate ordinal cut map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe v u v' u'

namespace CategoryTheory.CosimplicialObject.Cylinder

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type u'} [Category.{v'} A]

/-- The interval parameter, with its actual cosimplicial simplex factor. -/
def obj (Δ : CosimplicialObject C) : CosimplicialObject C :=
  Δ ⋙ prod.functor.obj (Δ.obj ⦋1⦌)

/-- A constant vertex of the interval, retaining the simplex factor. -/
def endpoint (Δ : CosimplicialObject C) (v : Fin 2) : Δ ⟶ obj Δ where
  app n := prod.lift (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 _)
  naturality m n f := by
    apply prod.hom_ext
    · simp only [obj, Functor.comp_map, prod.functor_obj_map, Category.assoc,
        prod.lift_fst, prod.map_fst, Category.comp_id]
      rw [← Δ.map_comp]
      congr 1
    · simp [obj]

/-- The `i`-th prism simplex as an actual map into interval times simplex. -/
def simplex (Δ : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    Δ.obj ⦋n + 1⦌ ⟶ (obj Δ).obj ⦋n⦌ :=
  prod.lift (Δ.map (SimplexCategory.toMk₁ i.castSucc.succ)) (Δ.σ i)

lemma simplex_zero_face (Δ : CosimplicialObject C) (n : ℕ) :
    Δ.δ 0 ≫ simplex Δ (0 : Fin (n + 1)) = (endpoint Δ 1).app ⦋n⦌ := by
  apply prod.hom_ext
  · simp only [simplex, endpoint, Category.assoc, prod.lift_fst, CosimplicialObject.δ]
    rw [← Δ.map_comp, SimplexCategory.δ_zero_comp_toMk₁_prism]
  · simp only [simplex, endpoint, Category.assoc, prod.lift_snd]
    exact Δ.δ_comp_σ_self (i := (0 : Fin (n + 1)))

lemma simplex_last_face (Δ : CosimplicialObject C) (n : ℕ) :
    Δ.δ (Fin.last (n + 1)) ≫ simplex Δ (Fin.last n) =
      (endpoint Δ 0).app ⦋n⦌ := by
  apply prod.hom_ext
  · simp only [simplex, endpoint, Category.assoc, prod.lift_fst, CosimplicialObject.δ]
    rw [← Δ.map_comp, SimplexCategory.δ_last_comp_toMk₁_prism]
  · simp only [simplex, endpoint, Category.assoc, prod.lift_snd]
    exact Δ.δ_comp_σ_succ (i := Fin.last n)

lemma simplex_face_left (Δ : CosimplicialObject C) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    Δ.δ i.castSucc ≫ simplex Δ j.succ = simplex Δ j ≫ (obj Δ).δ i := by
  apply prod.hom_ext
  · simp only [simplex, obj, CosimplicialObject.δ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, SimplexCategory.δ_castSucc_comp_toMk₁_prism i j hij]
  · simpa [Category.assoc, simplex, obj, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.δ_comp_σ_of_le hij

lemma simplex_face_middle (Δ : CosimplicialObject C) {n : ℕ} (j : Fin (n + 1)) :
    Δ.δ j.castSucc.succ ≫ simplex Δ j.succ =
      Δ.δ j.castSucc.succ ≫ simplex Δ j.castSucc := by
  apply prod.hom_ext
  · simp only [simplex, CosimplicialObject.δ, Category.assoc, prod.lift_fst]
    rw [← Δ.map_comp, ← Δ.map_comp, SimplexCategory.δ_middle_comp_toMk₁_prism]
  · simp only [simplex, Category.assoc, prod.lift_snd]
    exact (Δ.δ_comp_σ_self (i := j.succ)).trans (Δ.δ_comp_σ_succ (i := j.castSucc)).symm

lemma simplex_face_right (Δ : CosimplicialObject C) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    Δ.δ i.succ ≫ simplex Δ j.castSucc = simplex Δ j ≫ (obj Δ).δ i := by
  apply prod.hom_ext
  · simp only [simplex, obj, CosimplicialObject.δ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, SimplexCategory.δ_succ_comp_toMk₁_prism i j hji]
  · simpa [Category.assoc, simplex, obj, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.δ_comp_σ_of_gt hji

lemma simplex_degeneracy_left (Δ : CosimplicialObject C) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Δ.σ i.castSucc ≫ simplex Δ j = simplex Δ j.succ ≫ (obj Δ).σ i := by
  apply prod.hom_ext
  · simp only [simplex, obj, CosimplicialObject.σ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, SimplexCategory.σ_castSucc_comp_toMk₁_prism i j hij]
  · simpa [Category.assoc, simplex, obj, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.σ_comp_σ hij

lemma simplex_degeneracy_right (Δ : CosimplicialObject C) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    Δ.σ i.succ ≫ simplex Δ j = simplex Δ j.castSucc ≫ (obj Δ).σ i := by
  apply prod.hom_ext
  · simp only [simplex, obj, CosimplicialObject.σ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, SimplexCategory.σ_succ_comp_toMk₁_prism i j hji]
  · simpa [Category.assoc, simplex, obj, CosimplicialObject.δ, CosimplicialObject.σ] using
      (Δ.σ_comp_σ hji).symm

/-- The prism is a simplicial homotopy on the originally evaluated presheaf. -/
def simplicialHomotopy (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    SimplicialObject.Homotopy
      (whiskerRight (NatTrans.op (endpoint Δ 0)) P)
      (whiskerRight (NatTrans.op (endpoint Δ 1)) P) where
  h i := P.map (simplex Δ i).op
  h_zero_comp_δ_zero n := by
    change P.map (simplex Δ (0 : Fin (n + 1))).op ≫ P.map (Δ.δ 0).op =
      P.map ((endpoint Δ 1).app ⦋n⦌).op
    rw [← P.map_comp, ← op_comp, simplex_zero_face]
  h_last_comp_δ_last n := by
    change P.map (simplex Δ (Fin.last n)).op ≫ P.map (Δ.δ (Fin.last (n + 1))).op =
      P.map ((endpoint Δ 0).app ⦋n⦌).op
    rw [← P.map_comp, ← op_comp, simplex_last_face]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change P.map (simplex Δ j.succ).op ≫ P.map (Δ.δ i.castSucc).op =
      P.map ((obj Δ).δ i).op ≫ P.map (simplex Δ j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_left Δ i j hij]
  h_succ_comp_δ_castSucc_succ j := by
    change P.map (simplex Δ j.succ).op ≫ P.map (Δ.δ j.castSucc.succ).op =
      P.map (simplex Δ j.castSucc).op ≫ P.map (Δ.δ j.castSucc.succ).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_middle]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change P.map (simplex Δ j.castSucc).op ≫ P.map (Δ.δ i.succ).op =
      P.map ((obj Δ).δ i).op ≫ P.map (simplex Δ j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_right Δ i j hji]
  h_comp_σ_castSucc_of_le i j hij := by
    change P.map (simplex Δ j).op ≫ P.map (Δ.σ i.castSucc).op =
      P.map ((obj Δ).σ i).op ≫ P.map (simplex Δ j.succ).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_degeneracy_left Δ i j hij]
  h_comp_σ_succ_of_lt i j hji := by
    change P.map (simplex Δ j).op ≫ P.map (Δ.σ i.succ).op =
      P.map ((obj Δ).σ i).op ≫ P.map (simplex Δ j.castSucc).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_degeneracy_right Δ i j hji]

variable [Preadditive A]

/-- The native signed chain homotopy of the actual endpoint restrictions. -/
def endpointHomotopy (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    _root_.Homotopy
      ((alternatingFaceMapComplex A).map (whiskerRight (NatTrans.op (endpoint Δ 0)) P))
      ((alternatingFaceMapComplex A).map (whiskerRight (NatTrans.op (endpoint Δ 1)) P)) :=
  (simplicialHomotopy Δ P).toChainHomotopy

/-- The sign is Mathlib's negative alternating sum of the geometric prism pullbacks. -/
theorem endpointHomotopy_hom (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (endpointHomotopy Δ P).hom n (n + 1) =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • P.map (simplex Δ i).op :=
  SimplicialObject.Homotopy.ToChainHomotopy.hom_eq _ n

/-- The actual endpoint restrictions agree on every homology group. -/
theorem endpoint_homologyMap_eq [CategoryWithHomology A]
    (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex A).map (whiskerRight (NatTrans.op (endpoint Δ 0)) P)) n =
      HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex A).map (whiskerRight (NatTrans.op (endpoint Δ 1)) P)) n :=
  (endpointHomotopy Δ P).homologyMap_eq n

end CategoryTheory.CosimplicialObject.Cylinder
