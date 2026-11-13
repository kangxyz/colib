/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BoundaryRetraction
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Homeomorphism of the cube and simplex boundary pairs

The standard simplex is identified with the full-dimensional convex body of
nonnegative vectors of total mass at most one. Gauge rescaling between this
body and the closed unit cube gives a genuine homeomorphism carrying the cube
boundary exactly onto the zero-coordinate boundary of the standard simplex.
The construction includes dimension zero.
-/

open Topology Convexity.StdSimplex

/-! Implementation source: `Quillen/Topology/Cube/SimplexPair.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open Convexity Set
open scoped BigOperators Topology unitInterval

namespace Topology.Cube

/-- The full-dimensional simplex, with its zeroth barycentric coordinate omitted. -/
def simplexBody (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Restoring the omitted barycentric coordinate identifies the simplex body with
its usual standard-simplex model. -/
def simplexBodyHomeomorph (n : ℕ) :
    simplexBody n ≃ₜ StdSimplex ℝ (Fin (n + 1)) where
  toFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (1 - ∑ i, x.val i) x.val)
    nonneg i := by
      refine Fin.cases ?_ (fun j ↦ x.property.1 j) i
      exact sub_nonneg.mpr x.property.2
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ i : Fin (n + 1), Fin.cons (1 - ∑ j, x.val j) x.val i) = 1
      simp [Fin.sum_univ_succ] }
  invFun x := ⟨fun i ↦ x.weights i.succ, fun i ↦ x.weights_nonneg i.succ, by
    have h := x.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith [x.weights_nonneg 0]⟩
  left_inv x := by rfl
  right_inv x := by
    apply StdSimplex.ext
    ext i
    refine Fin.cases ?_ (fun j ↦ rfl) i
    change 1 - ∑ j : Fin n, x.weights j.succ = x.weights 0
    have h := x.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
    refine continuous_pi fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change Continuous (fun x : simplexBody n ↦ 1 - ∑ j, x.val j)
      fun_prop
    · change Continuous (fun x : simplexBody n ↦ x.val j)
      exact (continuous_apply j).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun i ↦ ?_
    exact StdSimplex.continuous_weights_apply ℝ i.succ

@[simp] theorem simplexBodyHomeomorph_weights_zero (n : ℕ) (x : simplexBody n) :
    (simplexBodyHomeomorph n x).weights 0 = 1 - ∑ i, x.val i := rfl

@[simp] theorem simplexBodyHomeomorph_weights_succ (n : ℕ) (x : simplexBody n) (i : Fin n) :
    (simplexBodyHomeomorph n x).weights i.succ = x.val i := rfl

/-- The original cube coordinates as a closed box in a real vector space. -/
def cubeBodyHomeomorph (n : ℕ) :
    (Fin n → I) ≃ₜ (Icc (0 : Fin n → ℝ) 1) where
  toFun x := ⟨fun i ↦ x i, fun i ↦ (x i).property.1, fun i ↦ (x i).property.2⟩
  invFun x i := ⟨x.val i, x.property.1 i, x.property.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i ↦ ?_
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

theorem convex_simplexBody (n : ℕ) : Convex ℝ (simplexBody n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  change ∑ i, (a * x i + b * y i) ≤ 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

theorem isClosed_simplexBody (n : ℕ) : IsClosed (simplexBody n) := by
  have h : simplexBody n = (⋂ i : Fin n, {x | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x
    simp [simplexBody]
  rw [h]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem simplexBody_subset_cube (n : ℕ) : simplexBody n ⊆ Icc (0 : Fin n → ℝ) 1 := by
  intro x hx
  refine ⟨hx.1, fun i ↦ ?_⟩
  exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans hx.2

theorem isCompact_simplexBody (n : ℕ) : IsCompact (simplexBody n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplexBody n) (simplexBody_subset_cube n)

/-- Strict positivity of all barycentric coordinates describes the interior. -/
theorem interior_simplexBody (n : ℕ) :
    interior (simplexBody n) = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  cases n with
  | zero =>
    have h : simplexBody 0 = univ := by ext x; simp [simplexBody]
    simp [h]
  | succ n =>
    let e : (Fin (n + 1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ) := {
      toFun x := (∑ i, x i, fun i ↦ x i.succ)
      invFun x := Fin.cons (x.1 - ∑ i, x.2 i) x.2
      left_inv x := by
        ext i
        refine Fin.cases ?_ (fun j ↦ rfl) i
        simp [Fin.sum_univ_succ]
      right_inv x := by
        apply Prod.ext
        · simp [Fin.sum_univ_succ]
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine continuous_pi fun i ↦ ?_
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ]
        · fun_prop
        · fun_prop }
    have hσ : IsOpenMap (fun x : Fin (n + 1) → ℝ ↦ ∑ i, x i) :=
      isOpenMap_fst.comp e.isOpenMap
    have h : simplexBody (n + 1) =
        (⋂ i : Fin (n + 1), (fun x : Fin (n + 1) → ℝ ↦ x i) ⁻¹' Ici 0) ∩
          (fun x ↦ ∑ i, x i) ⁻¹' Iic 1 := by
      ext x
      simp [simplexBody]
    rw [h, interior_inter, interior_iInter_of_finite]
    simp_rw [← IsOpenMap.preimage_interior_eq_interior_preimage
      (isOpenMap_eval _) (continuous_apply _), interior_Ici]
    rw [← hσ.preimage_interior_eq_interior_preimage (by fun_prop), interior_Iic]
    ext x
    simp

theorem interior_simplexBody_nonempty (n : ℕ) : (interior (simplexBody n)).Nonempty := by
  refine ⟨fun _ ↦ 1 / (n + 1 : ℝ), ?_⟩
  rw [interior_simplexBody]
  refine ⟨fun _ ↦ by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

theorem interior_cubeBody (n : ℕ) :
    interior (Icc (0 : Fin n → ℝ) 1) = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  rw [← pi_univ_Icc, interior_pi_set Set.finite_univ]
  ext x
  simp [interior_Icc]

theorem interior_cubeBody_nonempty (n : ℕ) :
    (interior (Icc (0 : Fin n → ℝ) 1)).Nonempty := by
  refine ⟨fun _ ↦ 1 / 2, ?_⟩
  rw [interior_cubeBody]
  norm_num

/-- An ambient homeomorphism carrying the actual cube and simplex frontiers onto
one another, obtained by gauge rescaling convex bodies. -/
theorem exists_cubeBody_simplexBody_homeomorph (n : ℕ) :
    ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      e '' Icc 0 1 = simplexBody n ∧
      e '' frontier (Icc 0 1) = frontier (simplexBody n) := by
  obtain ⟨e, -, hc, hf⟩ := exists_homeomorph_image_eq
    (convex_Icc (0 : Fin n → ℝ) 1) (interior_cubeBody_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ isCompact_Icc.isBounded)
    (convex_simplexBody n) (interior_simplexBody_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ (isCompact_simplexBody n).isBounded)
  refine ⟨e, ?_, hf⟩
  simpa [isClosed_Icc.closure_eq, (isClosed_simplexBody n).closure_eq] using hc

/-- The raw cubical boundary is exactly the ambient frontier of the closed box. -/
theorem cubeBodyHomeomorph_mem_frontier_iff (n : ℕ) (x : Fin n → I) :
    (cubeBodyHomeomorph n x).val ∈ frontier (Icc (0 : Fin n → ℝ) 1) ↔
      x ∈ _root_.Cube.boundary (Fin n) := by
  rw [isClosed_Icc.frontier_eq, Set.mem_sdiff, interior_cubeBody]
  simp only [(cubeBodyHomeomorph n x).property, true_and, Set.mem_ofPred_eq,
    _root_.Cube.boundary]
  change (¬ ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1) ↔ ∃ i, x i = 0 ∨ x i = 1
  constructor
  · intro h
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    by_cases hi₀ : 0 < (x i : ℝ)
    · right
      apply Subtype.ext
      exact le_antisymm (x i).property.2 (hi hi₀)
    · left
      apply Subtype.ext
      exact le_antisymm (le_of_not_gt hi₀) (x i).property.1
  · rintro ⟨i, hi | hi⟩ h
    · have := (h i).1
      simp [hi] at this
    · have := (h i).2
      simp [hi] at this

/-- The simplex body's frontier is the usual zero-coordinate simplex boundary. -/
theorem simplexBodyHomeomorph_mem_boundary_iff (n : ℕ) (x : simplexBody n) :
    simplexBodyHomeomorph n x ∈ Convexity.StdSimplex.boundary n ↔
      x.val ∈ frontier (simplexBody n) := by
  rw [(isClosed_simplexBody n).frontier_eq, Set.mem_sdiff, interior_simplexBody]
  simp only [x.property, true_and, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩ h
    refine Fin.cases ?_ (fun j hj ↦ ?_) i hi
    · intro hi
      change 1 - ∑ j, x.val j = 0 at hi
      linarith [h.2]
    · change x.val j = 0 at hj
      exact (ne_of_gt (h.1 j)) hj
  · intro h
    by_cases hs : ∑ i, x.val i < 1
    · have hz : ¬ ∀ i, 0 < x.val i := fun hz ↦ h ⟨hz, hs⟩
      push Not at hz
      obtain ⟨i, hi⟩ := hz
      exact ⟨i.succ, le_antisymm hi (x.property.1 i)⟩
    · refine ⟨0, ?_⟩
      change 1 - ∑ i, x.val i = 0
      linarith [x.property.2]

/-- There is a genuine homeomorphism of cube/simplex boundary pairs in every dimension. -/
theorem exists_simplexHomeomorph (n : ℕ) :
    ∃ e : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)),
      ∀ x, e x ∈ Convexity.StdSimplex.boundary n ↔ x ∈ _root_.Cube.boundary (Fin n) := by
  obtain ⟨e, he, hf⟩ := exists_cubeBody_simplexBody_homeomorph n
  have he' (x : Fin n → ℝ) : x ∈ Icc 0 1 ↔ e x ∈ simplexBody n := by
    rw [← he]
    exact (e.injective.mem_set_image).symm
  let e' := e.subtype he'
  refine ⟨(cubeBodyHomeomorph n).trans (e'.trans (simplexBodyHomeomorph n)), fun x ↦ ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, simplexBodyHomeomorph_mem_boundary_iff]
  change e (cubeBodyHomeomorph n x).val ∈ frontier (simplexBody n) ↔ _
  rw [← hf, e.injective.mem_set_image]
  exact cubeBodyHomeomorph_mem_frontier_iff n x

/-- A chosen actual homeomorphism of the standard cube with the standard simplex. -/
def simplexHomeomorph (n : ℕ) : (Fin n → I) ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (exists_simplexHomeomorph n).choose

@[simp] theorem simplexHomeomorph_mem_boundary_iff (n : ℕ) (x : Fin n → I) :
    simplexHomeomorph n x ∈ Convexity.StdSimplex.boundary n ↔ x ∈ _root_.Cube.boundary (Fin n) :=
  (exists_simplexHomeomorph n).choose_spec x

/-- The restriction to the actual boundary subspaces. -/
def simplexBoundaryHomeomorph (n : ℕ) :
    _root_.Cube.boundary (Fin n) ≃ₜ Convexity.StdSimplex.boundary n :=
  (simplexHomeomorph n).subtype (fun x ↦ (simplexHomeomorph_mem_boundary_iff n x).symm)

@[simp] theorem simplexBoundaryHomeomorph_val (n : ℕ)
    (x : _root_.Cube.boundary (Fin n)) :
    (simplexBoundaryHomeomorph n x).val = simplexHomeomorph n x.val := rfl

@[simp] theorem simplexBoundaryHomeomorph_symm_val (n : ℕ) (x : Convexity.StdSimplex.boundary n) :
    ((simplexBoundaryHomeomorph n).symm x).val = (simplexHomeomorph n).symm x.val := rfl

end Topology.Cube
