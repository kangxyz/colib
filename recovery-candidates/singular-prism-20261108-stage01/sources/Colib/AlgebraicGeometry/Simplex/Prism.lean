/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.SimplexCategory.Prism
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# The actual relative algebraic prism

The interval is the existing barycentric one-simplex, and all products are
the existing literal scheme fiber products. Vertex zero evaluates its two
coordinates at `(1, 0)` and vertex one at `(0, 1)`. Thus the retained coordinate
`t₀` in the existing polynomial chart takes the values one and zero respectively.
The order of the vertices is not silently exchanged when forming the homotopy.

The prism maps are the original product maps from `U × Δⁿ⁺¹` to
`(U × Δ¹) × Δⁿ`, using Mathlib's `toMk₁` and the actual codegeneracy maps.
There is no assumed homotopy invariance and no transfer action.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- Evaluation at an actual barycentric vertex of the algebraic interval. -/
def vertexEvaluation (v : Fin 2) : CoordinateRing R 1 →+* R :=
  lift (RingHom.id R) (fun i => if i = v then 1 else 0) (by simp)

@[simp]
theorem vertexEvaluation_constant (v : Fin 2) (r : R) :
    vertexEvaluation R v (constant R 1 r) = r := by simp [vertexEvaluation]

@[simp]
theorem vertexEvaluation_coordinate (v i : Fin 2) :
    vertexEvaluation R v (coordinate R 1 i) = if i = v then 1 else 0 := by
  simp [vertexEvaluation]

/-- The constant vertex map from an arbitrary actual smooth-site object. -/
def vertexAt (U : SmoothSite (Spec (.of R))) (v : Fin 2) : U ⟶ (cosimplicialSmoothSite R).obj ⦋1⦌ :=
  SmoothSite.homMk (U.hom ≫ Spec.map (CommRingCat.ofHom (vertexEvaluation R v))) (by
    change (U.hom ≫ Spec.map (CommRingCat.ofHom (vertexEvaluation R v))) ≫
      Spec.map (CommRingCat.ofHom (constant R 1)) = U.hom
    rw [Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (constant R 1) ≫
        CommRingCat.ofHom (vertexEvaluation R v) = 𝟙 (CommRingCat.of R) := by
      apply CommRingCat.hom_ext
      exact RingHom.ext (vertexEvaluation_constant R v)
    rw [h, Spec.map_id]
    exact Category.comp_id (show U.left ⟶ Spec (.of R) from U.hom))

@[reassoc (attr := simp)]
theorem comp_vertexAt {U V : SmoothSite (Spec (.of R))} (f : U ⟶ V) (v : Fin 2) :
    f ≫ vertexAt R V v = vertexAt R U v := by
  apply MorphismProperty.Over.Hom.ext
  change f.left ≫ (V.hom ≫ _) = U.hom ≫ _
  exact (Category.assoc f.left (show V.left ⟶ Spec (.of R) from V.hom)
    (Spec.map (CommRingCat.ofHom (vertexEvaluation R v)))).symm.trans
      (congrArg (fun g : U.left ⟶ Spec (.of R) =>
        g ≫ Spec.map (CommRingCat.ofHom (vertexEvaluation R v)))
          (MorphismProperty.Over.w f))

/-- The ordinal constant map is the original constant barycentric vertex map. -/
theorem map_const_eq_vertexAt (n : ℕ) (v : Fin 2) :
    (cosimplicialSmoothSite R).map (SimplexCategory.const ⦋n⦌ ⦋1⦌ v) =
      vertexAt R ((cosimplicialSmoothSite R).obj ⦋n⦌) v := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (pullback R
      (SimplexCategory.const ⦋n⦌ ⦋1⦌ v).toOrderHom)) =
    structureMap R n ≫ Spec.map (CommRingCat.ofHom (vertexEvaluation R v))
  rw [structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply ringHom_ext
  · intro r
    simp
  · intro i
    by_cases h : i = v
    · subst i
      simp [SimplexCategory.const]
    · simp [SimplexCategory.const, h, Ne.symm h]

/-- The original inclusion of either constant endpoint into `U × Δ¹`. -/
def intervalInclusion (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    U ⟶ SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌) :=
  SmoothSite.productLift (𝟙 U) (vertexAt R U v)

@[reassoc (attr := simp)]
theorem intervalInclusion_fst (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    intervalInclusion R U v ≫
      SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌) = 𝟙 U := by
  simp [intervalInclusion]

@[reassoc (attr := simp)]
theorem intervalInclusion_snd (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    intervalInclusion R U v ≫ SmoothSite.productSnd U ((cosimplicialSmoothSite R).obj ⦋1⦌) =
      vertexAt R U v := by simp [intervalInclusion]

theorem productMap_id_const (U : SmoothSite (Spec (.of R))) (n : ℕ) (v : Fin 2) :
    SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map (SimplexCategory.const ⦋n⦌ ⦋1⦌ v)) =
        SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋n⦌) ≫ intervalInclusion R U v := by
  rw [map_const_eq_vertexAt]
  apply SmoothSite.product_hom_ext <;> simp

/-- The literal `i`-th relative prism simplex. -/
@[colib_ref "MVW2006" "Lecture 2, Definition 2.17, p. 17"
  "generalization" "Actual relative algebraic prism over every commutative base ring",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Aglib/Algebra/Homology/SingularComplex/Endpoints.lean:49-53"
    "adaptation" "Prism simplex with literal relative products and the native ordinal cut"]
def prismMap (U : SmoothSite (Spec (.of R))) {n : ℕ} (i : Fin (n + 1)) :
    SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ⟶
      SmoothSite.product (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌))
        ((cosimplicialSmoothSite R).obj ⦋n⦌) :=
  SmoothSite.productLift
    (SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map (SimplexCategory.toMk₁ i.castSucc.succ)))
    (SmoothSite.productSnd U ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ≫
      (cosimplicialSmoothSite R).σ i)

@[reassoc (attr := simp)]
theorem prismMap_fst (U : SmoothSite (Spec (.of R))) {n : ℕ} (i : Fin (n + 1)) :
    prismMap R U i ≫ SmoothSite.productFst _ _ =
      SmoothSite.productMap (𝟙 U)
        ((cosimplicialSmoothSite R).map (SimplexCategory.toMk₁ i.castSucc.succ)) := by
  simp [prismMap]

@[reassoc (attr := simp)]
theorem prismMap_snd (U : SmoothSite (Spec (.of R))) {n : ℕ} (i : Fin (n + 1)) :
    prismMap R U i ≫ SmoothSite.productSnd _ _ =
      SmoothSite.productSnd U ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ≫
        (cosimplicialSmoothSite R).σ i := by
  simp [prismMap]

theorem prismMap_zero_face (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ (0 : Fin (n + 2))) ≫
      prismMap R U (0 : Fin (n + 1)) =
        SmoothSite.productMap (intervalInclusion R U 1)
          (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌)) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.δ_zero_comp_toMk₁_prism]
    exact productMap_id_const R U n 1
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd_assoc,
      SmoothSite.productMap_snd, Category.comp_id]
    exact (congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n⦌) ≫ f)
        ((cosimplicialSmoothSite R).δ_comp_σ_self (i := (0 : Fin (n + 1))))).trans
          (Category.comp_id _)

theorem prismMap_last_face (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ (Fin.last (n + 1))) ≫
      prismMap R U (Fin.last n) =
        SmoothSite.productMap (intervalInclusion R U 0)
          (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌)) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.δ_last_comp_toMk₁_prism]
    exact productMap_id_const R U n 0
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd_assoc,
      SmoothSite.productMap_snd, Category.comp_id]
    exact (congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n⦌) ≫ f)
        ((cosimplicialSmoothSite R).δ_comp_σ_succ (i := Fin.last n))).trans
          (Category.comp_id _)

theorem prismMap_face_left (U : SmoothSite (Spec (.of R))) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ i.castSucc) ≫
      prismMap R U j.succ = prismMap R U j ≫
        SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).δ i) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst,
      Category.comp_id]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.δ_castSucc_comp_toMk₁_prism i j hij]
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd,
      SmoothSite.productMap_snd_assoc, prismMap_snd_assoc]
    exact congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ≫ f)
        ((cosimplicialSmoothSite R).δ_comp_σ_of_le hij)

theorem prismMap_face_middle (U : SmoothSite (Spec (.of R))) {n : ℕ}
    (j : Fin (n + 1)) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ j.castSucc.succ) ≫
      prismMap R U j.succ =
        SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ j.castSucc.succ) ≫
          prismMap R U j.castSucc := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst]
    rw [← SmoothSite.productMap_comp, ← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) =
        SmoothSite.productMap (𝟙 U)
          ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _)
    rw [← Functor.map_comp, ← Functor.map_comp,
      SimplexCategory.δ_middle_comp_toMk₁_prism]
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd_assoc]
    exact congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ≫ f)
        (((cosimplicialSmoothSite R).δ_comp_σ_self (i := j.succ)).trans
          ((cosimplicialSmoothSite R).δ_comp_σ_succ (i := j.castSucc)).symm)

theorem prismMap_face_right (U : SmoothSite (Spec (.of R))) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ i.succ) ≫
      prismMap R U j.castSucc = prismMap R U j ≫
        SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).δ i) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst,
      Category.comp_id]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.δ_succ_comp_toMk₁_prism i j hji]
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd,
      SmoothSite.productMap_snd_assoc, prismMap_snd_assoc]
    exact congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n + 1⦌) ≫ f)
        ((cosimplicialSmoothSite R).δ_comp_σ_of_gt hji)

theorem prismMap_degeneracy_left (U : SmoothSite (Spec (.of R))) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).σ i.castSucc) ≫
      prismMap R U j = prismMap R U j.succ ≫
        SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).σ i) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst,
      Category.comp_id]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.σ_castSucc_comp_toMk₁_prism i j hij]
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd,
      SmoothSite.productMap_snd_assoc, prismMap_snd_assoc]
    exact congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n + 1 + 1⦌) ≫ f)
        ((cosimplicialSmoothSite R).σ_comp_σ hij)

theorem prismMap_degeneracy_right (U : SmoothSite (Spec (.of R))) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).σ i.succ) ≫
      prismMap R U j = prismMap R U j.castSucc ≫
        SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).σ i) := by
  apply SmoothSite.product_hom_ext
  · simp only [Category.assoc, prismMap_fst, SmoothSite.productMap_fst,
      Category.comp_id]
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    change SmoothSite.productMap (𝟙 U)
      ((cosimplicialSmoothSite R).map _ ≫ (cosimplicialSmoothSite R).map _) = _
    rw [← Functor.map_comp, SimplexCategory.σ_succ_comp_toMk₁_prism i j hji]
  · simp only [Category.assoc, prismMap_snd, SmoothSite.productMap_snd,
      SmoothSite.productMap_snd_assoc, prismMap_snd_assoc]
    exact congrArg (fun f => SmoothSite.productSnd U
      ((cosimplicialSmoothSite R).obj ⦋n + 1 + 1⦌) ≫ f)
        ((cosimplicialSmoothSite R).σ_comp_σ hji).symm

end AlgebraicSimplex
