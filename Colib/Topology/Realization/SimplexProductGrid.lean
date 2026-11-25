/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.Topology.Realization.ProductSimplex

/-!
# The realized standard simplex grid and its rows and columns

The grid is the actual product of two simplicial standard simplices. Its monotone
lexicographic embedding yields the barycentric parameter through the native realization
homeomorphism. Evaluating a whole row or column is the given affine face map.

Adapted from the original Quillen files under `Quillen/Topology/Realization` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:
`SimplexProductParameter.lean:19-71`, `SimplexGridBoundary.lean:18-71`,
and `SimplexGridColumn.lean:18-68`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity Opposite SSet
open scoped Simplicial Topology
universe u

namespace Topology.SimplexGrid

/-- Dimension of the simplex with one vertex for every ordered pair of grid vertices. -/
def dimension (p q : ℕ) : ℕ := p * (q + 1) + q

/-- A monotone lexicographic enumeration of the product grid. -/
def index (p q : ℕ) : Fin (p + 1) × Fin (q + 1) →o Fin (dimension p q + 1) where
  toFun z := ⟨z.1.val * (q + 1) + z.2.val, by
    have hi := Nat.le_of_lt_succ z.1.isLt
    have hj := z.2.isLt
    have h := Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right (q + 1) hi) hj
    simpa only [dimension, Nat.add_assoc] using h⟩
  monotone' _ _ h := Nat.add_le_add (Nat.mul_le_mul_right (q + 1) h.1) h.2

/-- The grid enumeration is a bijection of vertex sets; its inverse is used only on vertices. -/
def indexEquiv (p q : ℕ) :
    Fin (p + 1) × Fin (q + 1) ≃ Fin (dimension p q + 1) :=
  finProdFinEquiv.trans (finCongr (by simp [dimension, Nat.add_mul, Nat.add_assoc]))

/-- The order hom and the vertex equivalence have the same enumeration. -/
theorem index_eq_equiv (p q : ℕ) (z : Fin (p + 1) × Fin (q + 1)) :
    index p q z = indexEquiv p q z := by
  apply Fin.ext
  change z.1.val * (q + 1) + z.2.val = z.2.val + (q + 1) * z.1.val
  ac_rfl

/-- Decode each original ordered grid vertex. -/
@[simp] theorem decode_index (p q : ℕ) (z : Fin (p + 1) × Fin (q + 1)) :
    (indexEquiv p q).symm (index p q z) = z := by
  rw [index_eq_equiv, Equiv.symm_apply_apply]

/-- Literal simplicial grid embedding into its linearly ordered common vertex set. -/
def embedding (p q : ℕ) : (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[dimension p q] where
  app n := ↾fun z ↦ SSet.stdSimplex.objMk
    ((index p q).comp (SSet.prodStdSimplex.objEquiv z))
  naturality _ _ _ := by
    ext z : 4
    rfl

/-- The product parameter uses the actual inverse realization product homeomorphism. -/
def parameter (p q : ℕ) :
    C(StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)),
      StdSimplex ℝ (Fin (dimension p q + 1))) :=
  ⟨fun z ↦ SimplexCategory.toTopHomeo.{u} ⦋dimension p q⦌
    (SSet.toTop.map (embedding p q) ((realizationProductSimplexHomeomorph p q).symm z)),
    by fun_prop⟩

/-- Retain the whole original realization coordinate when entering the common simplex. -/
theorem parameter_realization (p q : ℕ) (z : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    parameter.{u} p q (realizationProductSimplexHomeomorph p q z) =
      SimplexCategory.toTopHomeo.{u} ⦋dimension p q⦌ (SSet.toTop.map (embedding p q) z) := by
  change SimplexCategory.toTopHomeo _
    (SSet.toTop.map (embedding p q)
      ((realizationProductSimplexHomeomorph p q).symm
        (realizationProductSimplexHomeomorph p q z))) = _
  rw [Homeomorph.symm_apply_apply]

/-- The simplex map sending every vertex of the source simplex to vertex `i`. -/
def constantFace {p q : ℕ} (i : Fin (p + 1)) : ⦋q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩

/-- The simplex map selecting grid vertices `(i, j)` with first coordinate fixed to `i`. -/
def rowFace (p q : ℕ) (i : Fin (p + 1)) : ⦋q⦌ ⟶ ⦋dimension p q⦌ :=
  SimplexCategory.Hom.mk ⟨fun j ↦ index p q (i, j),
    fun _ _ h ↦ (index p q).monotone ⟨le_rfl, h⟩⟩

/-- The simplicial inclusion of the row with first coordinate equal to vertex `i` and second
coordinate varying in `Δ[q]`.
-/
def row (p q : ℕ) (i : Fin (p + 1)) : (Δ[q] : SSet.{u}) ⟶ Δ[p] ⊗ Δ[q] :=
  lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _)

/-- The simplicial grid embedding restricts to the actual row face. -/
theorem row_embedding (p q : ℕ) (i : Fin (p + 1)) :
    row.{u} p q i ≫ embedding p q = SSet.stdSimplex.map (rowFace p q i) := by
  ext n z : 4
  rfl

/-- The product homeomorphism identifies the simplicial row with the literal fixed vertex. -/
theorem homeomorph_row (p q : ℕ) (i : Fin (p + 1)) (w : |(Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p q (SSet.toTop.map (row p q i) w) =
      (StdSimplex.single i, SimplexCategory.toTopHomeo ⦋q⦌ w) := by
  rw [realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (fst Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p⦌
      (SSet.toTop.map (lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _) ≫ fst _ _) w) = _
    rw [lift_fst, SimplexCategory.toTopHomeo_naturality_apply]
    exact StdSimplex.map_const _ i
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (snd Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q⦌
      (SSet.toTop.map (lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _) ≫ snd _ _) w) = _
    rw [lift_snd, CategoryTheory.Functor.map_id]
    rfl

/-- A whole row of the actual realized product parameter is the original affine simplex face. -/
theorem parameter_row (p q : ℕ) (i : Fin (p + 1)) (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter.{u} p q (StdSimplex.single i, w) = StdSimplex.map (rowFace p q i).toOrderHom w := by
  have h := parameter_realization p q
    (SSet.toTop.map (row.{u} p q i) ((SimplexCategory.toTopHomeo ⦋q⦌).symm w))
  rw [homeomorph_row, Homeomorph.apply_symm_apply] at h
  change parameter p q (StdSimplex.single i, w) =
    SimplexCategory.toTopHomeo ⦋dimension p q⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (embedding p q))
        ((SimplexCategory.toTopHomeo ⦋q⦌).symm w)) at h
  rw [← Functor.map_comp, row_embedding, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply] at h
  exact h

/-- The simplex map selecting grid vertices `(i, j)` with second coordinate fixed to `j`. -/
def columnFace (p q : ℕ) (j : Fin (q + 1)) : ⦋p⦌ ⟶ ⦋dimension p q⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ index p q (i, j),
    fun _ _ h ↦ (index p q).monotone ⟨h, le_rfl⟩⟩

/-- The simplicial inclusion of the column with second coordinate equal to vertex `j` and first
coordinate varying in `Δ[p]`.
-/
def column (p q : ℕ) (j : Fin (q + 1)) : (Δ[p] : SSet.{u}) ⟶ Δ[p] ⊗ Δ[q] :=
  lift (𝟙 _) (SSet.stdSimplex.map (constantFace j))

/-- The simplicial grid embedding restricts to the actual column face. -/
theorem column_embedding (p q : ℕ) (j : Fin (q + 1)) :
    column.{u} p q j ≫ embedding p q = SSet.stdSimplex.map (columnFace p q j) := by
  ext n z : 4
  rfl

/-- The actual product homeomorphism restricts to the literal fixed column. -/
theorem homeomorph_column (p q : ℕ) (j : Fin (q + 1)) (w : |(Δ[p] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p q (SSet.toTop.map (column p q j) w) =
      (SimplexCategory.toTopHomeo ⦋p⦌ w, StdSimplex.single j) := by
  rw [realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (fst Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p⦌
      (SSet.toTop.map (lift (𝟙 _) (SSet.stdSimplex.map (constantFace j)) ≫ fst _ _) w) = _
    rw [lift_fst, CategoryTheory.Functor.map_id]
    rfl
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (snd Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q⦌
      (SSet.toTop.map (lift (𝟙 _) (SSet.stdSimplex.map (constantFace j)) ≫ snd _ _) w) = _
    rw [lift_snd, SimplexCategory.toTopHomeo_naturality_apply]
    exact StdSimplex.map_const _ j

/-- The whole actual column parameter equals its affine simplex face, with no weight assumption. -/
theorem parameter_column (p q : ℕ) (j : Fin (q + 1)) (w : StdSimplex ℝ (Fin (p + 1))) :
    parameter.{u} p q (w, StdSimplex.single j) =
      StdSimplex.map (columnFace p q j).toOrderHom w := by
  have h := parameter_realization p q
    (SSet.toTop.map (column.{u} p q j) ((SimplexCategory.toTopHomeo ⦋p⦌).symm w))
  rw [homeomorph_column, Homeomorph.apply_symm_apply] at h
  change parameter p q (w, StdSimplex.single j) =
    SimplexCategory.toTopHomeo ⦋dimension p q⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (embedding p q))
        ((SimplexCategory.toTopHomeo ⦋p⦌).symm w)) at h
  rw [← Functor.map_comp, column_embedding, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply] at h
  exact h

end Topology.SimplexGrid
