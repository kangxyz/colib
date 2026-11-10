/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Simplex.NativeAction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Actual signed correspondence maps on singular chains

Literal products with the existing algebraic simplex form the cosimplicial
correspondence object. Actual graph interchange makes every signed exterior
map natural in all simplex operators. The chain complex and induced maps are
Mathlib's alternating-face construction itself, not new generic wrappers.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Singular/Maps.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380. This layer needs graph interchange,
but not the still-separate law for two arbitrary exterior correspondences.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe v u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The actual product simplex with operators given by their genuine graph correspondences. -/
def simplexProductCosimplicial (X : Cor k) : CosimplicialObject (Cor k) where
  obj n := (graphFunctor k).obj (SmoothSite.product X.toSmoothSite
    ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n))
  map f := (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
    ((AlgebraicSimplex.cosimplicialSmoothSite k).map f))
  map_id n := by simp
  map_comp f g := by
    rw [← Functor.map_comp]
    congr 1
    rw [← SmoothSite.productMap_comp, Category.id_comp]
    congr 1
    exact (AlgebraicSimplex.cosimplicialSmoothSite k).map_comp f g

@[simp]
theorem simplexProductCosimplicial_obj (X : Cor k) (n : ℕ) :
    (simplexProductCosimplicial X).obj ⦋n⦌ = simplexProduct X n := rfl

/-- Every simplex operator acts by the graph of the original literal product map. -/
theorem simplexProductCosimplicial_map (X : Cor k) {n m : SimplexCategory} (f : n ⟶ m) :
    (simplexProductCosimplicial X).map f =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((AlgebraicSimplex.cosimplicialSmoothSite k).map f)) := rfl

@[simp]
theorem simplexProductCosimplicial_δ (X : Cor k) {n : ℕ} (i : Fin (n + 2)) :
    (simplexProductCosimplicial X).δ i =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i)) := rfl

/-- Actual mixed graph interchange supplies naturality for every signed correspondence. -/
def simplexExteriorNatTrans {X Y : Cor k} (α : X ⟶ Y) :
    simplexProductCosimplicial X ⟶ simplexProductCosimplicial Y where
  app n := simplexExterior n.len α
  naturality _n _m f :=
    (simplexExterior_graph_interchange
      ((AlgebraicSimplex.cosimplicialSmoothSite k).map f) α).symm

@[simp]
theorem simplexExteriorNatTrans_app {X Y : Cor k} (α : X ⟶ Y) (n : ℕ) :
    (simplexExteriorNatTrans α).app ⦋n⦌ = simplexExterior n α := rfl

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Mathlib's all-degree alternating-face complex on the actual simplex product. -/
def singularObj (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    ChainComplex AddCommGrpCat.{v} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat.{v}).obj
    ((Cor.simplexProductCosimplicial X).op ⋙ P.obj)

@[simp]
theorem singularObj_X (P : PresheafWithTransfers.{v} k) (X : Cor k) (n : ℕ) :
    (singularObj P X).X n = sections P (Cor.simplexProduct X n) := rfl

/-- The original alternating coface transfers, in their original order and signs. -/
theorem singularObj_d (P : PresheafWithTransfers.{v} k) (X : Cor k) (n : ℕ) :
    (singularObj P X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
          ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  AlternatingFaceMapComplex.obj_d_eq
    ((Cor.simplexProductCosimplicial X).op ⋙ P.obj) n

/-- An arbitrary signed correspondence gives the actual contravariant chain map. -/
def singularTransfer (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y) :
    singularObj P Y ⟶ singularObj P X :=
  (alternatingFaceMapComplex AddCommGrpCat.{v}).map
    (Functor.whiskerRight (NatTrans.op (Cor.simplexExteriorNatTrans α)) P.obj)

@[simp]
theorem singularTransfer_f (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) (n : ℕ) :
    (singularTransfer P α).f n = transfer P (Cor.simplexExterior n α) := rfl

/-- Every original differential commutes with the exterior transfer. -/
theorem singularTransfer_comm (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) (i j : ℕ) :
    transfer P (Cor.simplexExterior i α) ≫ (singularObj P X).d i j =
      (singularObj P Y).d i j ≫ transfer P (Cor.simplexExterior j α) :=
  (singularTransfer P α).comm i j

@[simp]
theorem singularTransfer_zero (P : PresheafWithTransfers.{v} k) (X Y : Cor k) :
    singularTransfer P (0 : X ⟶ Y) = 0 := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (0 : X ⟶ Y)) = 0
  simp

@[simp]
theorem singularTransfer_add (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α β : X ⟶ Y) :
    singularTransfer P (α + β) = singularTransfer P α + singularTransfer P β := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (α + β)) =
    transfer P (Cor.simplexExterior n α) + transfer P (Cor.simplexExterior n β)
  simp

@[simp]
theorem singularTransfer_neg (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) : singularTransfer P (-α) = -singularTransfer P α := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (-α)) = -transfer P (Cor.simplexExterior n α)
  simp

@[simp]
theorem singularTransfer_zsmul (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (m : ℤ) (α : X ⟶ Y) : singularTransfer P (m • α) = m • singularTransfer P α := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (m • α)) = m • transfer P (Cor.simplexExterior n α)
  simp

end AlgebraicGeometry.PresheafWithTransfers
