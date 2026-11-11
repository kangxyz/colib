/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.Boundary
public import Colib.Topology.HELP.FiniteCharacterization
public import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Finite cube lifting for actual realized simplex boundaries

The native geometric simplex is identified with the convex corner obtained by
omitting its zeroth barycentric coordinate. The corner and the cube have
nonempty interiors, and their frontiers are their coordinate boundaries.
Mathlib's gauge-rescaling homeomorphism therefore identifies the two pairs.
This transports literal finite cube-boundary lifting to the actual realized
simplicial boundary, including dimension zero.

Only the finite cube characterization of weak homotopy equivalences is used;
no compact HELP or homotopy inverse is assumed.
-/

@[expose] public section

open Topology Set Convexity CategoryTheory
open scoped Simplicial
open scoped BigOperators
noncomputable section
namespace Topology.RealizedSimplexBoundary

private def corner (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

private def simplexCornerHomeomorph (n : ℕ) :
    StdSimplex ℝ (Fin (n + 1)) ≃ₜ corner n where
  toFun x := ⟨fun i ↦ x.weights i.succ, (fun i ↦ x.weights_nonneg i.succ),
    by have h := x.total_of_fintype; rw [Fin.sum_univ_succ] at h
       linarith [x.weights_nonneg 0]⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cases (1 - ∑ i, x.val i) x.val)
    nonneg := by
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using sub_nonneg.mpr x.property.2
      · simpa using x.property.1 j
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ] }
  left_inv x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change 1 - ∑ i : Fin n, x.weights i.succ = x.weights 0
      have h := x.total_of_fintype
      rw [Fin.sum_univ_succ] at h
      linarith
    · simp
  right_inv x := by ext i; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.mpr
    refine continuous_pi fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change Continuous fun x : corner n ↦ 1 - ∑ i, x.val i
      fun_prop
    · change Continuous fun x : corner n ↦ x.val j
      exact (continuous_apply j).comp continuous_subtype_val

private theorem simplexCornerHomeomorph_boundary (n : ℕ)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    x ∈ StdSimplex.boundary n ↔
      (∑ i, (simplexCornerHomeomorph n x).val i = 1) ∨
        ∃ i, (simplexCornerHomeomorph n x).val i = 0 := by
  have h := x.total_of_fintype
  rw [Fin.sum_univ_succ] at h
  change (∃ i, x.weights i = 0) ↔
    (∑ i : Fin n, x.weights i.succ = 1) ∨ ∃ i : Fin n, x.weights i.succ = 0
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases ?_ (fun j hj ↦ Or.inr ⟨j, hj⟩) i hi
    intro hi
    exact Or.inl (by linarith)
  · rintro (hx | ⟨i, hi⟩)
    · exact ⟨0, by linarith⟩
    · exact ⟨i.succ, hi⟩

private def sumCoordinateHomeomorph (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ₜ (Fin (n + 1) → ℝ) where
  toFun x := Fin.cases (∑ i, x i) (fun i ↦ x i.succ)
  invFun x := Fin.cases (x 0 - ∑ i : Fin n, x i.succ) (fun i ↦ x i.succ)
  left_inv x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [Fin.sum_univ_succ]
    · simp
  right_inv x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [Fin.sum_univ_succ]
    · simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> dsimp <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> dsimp <;> fun_prop

private theorem isOpenMap_sum (n : ℕ) :
    IsOpenMap (fun x : Fin (n + 1) → ℝ ↦ ∑ i, x i) :=
  (isOpenMap_eval (0 : Fin (n + 1))).comp (sumCoordinateHomeomorph n).isOpenMap

private theorem corner_eq (n : ℕ) : corner n =
    (⋂ i : Fin n, (fun x : Fin n → ℝ ↦ x i) ⁻¹' Ici 0) ∩
      (fun x ↦ ∑ i, x i) ⁻¹' Iic 1 := by
  ext x
  simp [corner]

private theorem interior_corner (n : ℕ) : interior (corner n) =
    {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  cases n with
  | zero =>
    have h : corner 0 = univ := by ext x; simp [corner]
    simp [h]
  | succ n =>
    rw [corner_eq, interior_inter, interior_iInter_of_finite]
    have he (i : Fin (n + 1)) :
        interior ((fun x : Fin (n + 1) → ℝ ↦ x i) ⁻¹' Ici 0) =
          (fun x ↦ x i) ⁻¹' Ioi 0 := by
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage
        (continuous_apply i), interior_Ici]
    simp only [he]
    rw [← (isOpenMap_sum n).preimage_interior_eq_interior_preimage
      (by fun_prop), interior_Iic]
    ext x
    simp

private theorem isClosed_corner (n : ℕ) : IsClosed (corner n) := by
  rw [corner_eq]
  apply IsClosed.inter
  · exact isClosed_iInter fun i ↦ isClosed_Ici.preimage (continuous_apply i)
  · apply isClosed_Iic.preimage
    fun_prop

private theorem corner_subset_Icc (n : ℕ) : corner n ⊆ Icc 0 1 := by
  intro x hx
  refine ⟨hx.1, fun i ↦ ?_⟩
  exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans hx.2

private theorem isCompact_corner (n : ℕ) : IsCompact (corner n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_corner n) (corner_subset_Icc n)

private theorem simplexCornerHomeomorph_frontier (n : ℕ)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    x ∈ StdSimplex.boundary n ↔
      (simplexCornerHomeomorph n x).val ∈ frontier (corner n) := by
  rw [simplexCornerHomeomorph_boundary, frontier, (isClosed_corner n).closure_eq,
    interior_corner]
  have hx := (simplexCornerHomeomorph n x).property
  simp only [mem_sdiff, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨hx, ?_⟩
    rintro ⟨hpos, hsum⟩
    rcases h with hs | ⟨i, hi⟩
    · exact (ne_of_lt hsum) hs
    · exact (ne_of_gt (hpos i)) hi
  · rintro ⟨_, hh⟩
    by_cases hsum : ∑ i, (simplexCornerHomeomorph n x).val i = 1
    · exact Or.inl hsum
    · right
      by_contra h
      push Not at h
      exact hh ⟨fun i ↦ lt_of_le_of_ne (hx.1 i) (h i).symm,
        lt_of_le_of_ne hx.2 hsum⟩

private def cubeAmbientHomeomorph (n : ℕ) :
    (Fin n → unitInterval) ≃ₜ Icc (0 : Fin n → ℝ) 1 where
  toFun x := ⟨fun i ↦ x i, (fun i ↦ (x i).property.1), fun i ↦ (x i).property.2⟩
  invFun x i := ⟨x.val i, x.property.1 i, x.property.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    exact continuous_pi fun i ↦ ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

private theorem interior_cube (n : ℕ) :
    interior (Icc (0 : Fin n → ℝ) 1) = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  have h : Icc (0 : Fin n → ℝ) 1 =
      ⋂ i : Fin n, (fun x : Fin n → ℝ ↦ x i) ⁻¹' Icc (0 : ℝ) 1 := by
    ext x
    simp [Pi.le_def, forall_and]
  rw [h, interior_iInter_of_finite]
  have he (i : Fin n) :
      interior ((fun x : Fin n → ℝ ↦ x i) ⁻¹' Icc 0 1) =
        (fun x ↦ x i) ⁻¹' Ioo 0 1 := by
    rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage
      (continuous_apply i), interior_Icc]
  simp only [he]
  ext x
  simp

private theorem cubeAmbientHomeomorph_frontier (n : ℕ) (x : Fin n → unitInterval) :
    x ∈ _root_.Cube.boundary (Fin n) ↔
      (cubeAmbientHomeomorph n x).val ∈ frontier (Icc (0 : Fin n → ℝ) 1) := by
  rw [frontier, isClosed_Icc.closure_eq, interior_cube]
  change (∃ i, x i = 0 ∨ x i = 1) ↔
    ((cubeAmbientHomeomorph n x).val ∈ Icc 0 1 ∧
      ¬ ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1)
  rw [and_iff_right (cubeAmbientHomeomorph n x).property]
  simp only [not_forall, not_and_or, not_lt]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (by simp [hi])⟩
    · exact ⟨i, Or.inr (by simp [hi])⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (Subtype.ext (le_antisymm hi (x i).property.1))⟩
    · exact ⟨i, Or.inr (Subtype.ext (le_antisymm (x i).property.2 hi))⟩

private theorem convex_corner (n : ℕ) : Convex ℝ (corner n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  change ∑ i, (a * x i + b * y i) ≤ 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = 1 := by simpa using hab

private theorem interior_corner_nonempty (n : ℕ) : (interior (corner n)).Nonempty := by
  rw [interior_corner]
  refine ⟨fun _ ↦ 1 / ((n : ℝ) + 1), ?_, ?_⟩
  · intro i
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)

private theorem interior_cube_nonempty (n : ℕ) :
    (interior (Icc (0 : Fin n → ℝ) 1)).Nonempty := by
  rw [interior_cube]
  exact ⟨fun _ ↦ 1 / 2, fun _ ↦ by norm_num⟩

private theorem exists_ambientComparison (n : ℕ) :
    ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      e '' corner n = Icc 0 1 ∧ e '' frontier (corner n) = frontier (Icc 0 1) := by
  obtain ⟨e, _, hc, hf⟩ := exists_homeomorph_image_eq
    (convex_corner n) (interior_corner_nonempty n) ((isCompact_corner n).isVonNBounded ℝ)
    (convex_Icc (0 : Fin n → ℝ) 1) (interior_cube_nonempty n)
    (isCompact_Icc.isVonNBounded ℝ)
  exact ⟨e, by simpa only [(isClosed_corner n).closure_eq, isClosed_Icc.closure_eq] using hc, hf⟩

private def ambientComparison (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_ambientComparison n).choose

private theorem ambientComparison_image (n : ℕ) :
    ambientComparison n '' corner n = Icc 0 1 :=
  (exists_ambientComparison n).choose_spec.1

private theorem ambientComparison_frontier (n : ℕ) :
    ambientComparison n '' frontier (corner n) = frontier (Icc 0 1) :=
  (exists_ambientComparison n).choose_spec.2

private def cornerCubeHomeomorph (n : ℕ) : corner n ≃ₜ Icc (0 : Fin n → ℝ) 1 :=
  ((ambientComparison n).image (corner n)).trans
    (Homeomorph.setCongr (ambientComparison_image n))

/-- A homeomorphism from the native geometric simplex to the literal finite cube. -/
private def simplexCubeHomeomorph (n : ℕ) :
    StdSimplex ℝ (Fin (n + 1)) ≃ₜ (Fin n → unitInterval) :=
  (simplexCornerHomeomorph n).trans
    ((cornerCubeHomeomorph n).trans (cubeAmbientHomeomorph n).symm)

/-- The comparison carries the original simplex boundary to the cube boundary. -/
private theorem simplexCubeHomeomorph_boundary (n : ℕ) (x : StdSimplex ℝ (Fin (n + 1))) :
    x ∈ StdSimplex.boundary n ↔ simplexCubeHomeomorph n x ∈ _root_.Cube.boundary (Fin n) := by
  rw [simplexCornerHomeomorph_frontier, cubeAmbientHomeomorph_frontier]
  change (simplexCornerHomeomorph n x).val ∈ frontier (corner n) ↔
    ((cubeAmbientHomeomorph n) ((cubeAmbientHomeomorph n).symm
      ((cornerCubeHomeomorph n) (simplexCornerHomeomorph n x)))).val ∈ _
  rw [Homeomorph.apply_symm_apply]
  change _ ↔ ambientComparison n (simplexCornerHomeomorph n x).val ∈ _
  rw [← ambientComparison_frontier]
  exact (ambientComparison n).injective.mem_set_image.symm

end Topology.RealizedSimplexBoundary

namespace Topology.CubicalSubdivision

universe u

/-- Finite cube-boundary lifting transports to the actual realized simplicial boundary. -/
theorem BoundaryLifting.hasLiftingProperty_realizationBoundary
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p) (n : ℕ) :
    HasLiftingProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
      (TopCat.ofHom p) where
  sq_hasLift {a b} sq := by
    let e := (SimplexCategory.toTopHomeo ⦋n⦌).trans
      (RealizedSimplexBoundary.simplexCubeHomeomorph n)
    let d := (SSet.realizationBoundaryHomeomorph n).trans
      ((RealizedSimplexBoundary.simplexCubeHomeomorph n).subtype
        (RealizedSimplexBoundary.simplexCubeHomeomorph_boundary n))
    have hpair (x : |(∂Δ[n] : SSet.{u})|) :
        e (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})) x) = (d x).val := rfl
    have hpair_symm (t : Boundary n) :
        e.symm t.val = SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})) (d.symm t) := by
      apply e.injective
      rw [Homeomorph.apply_symm_apply, hpair, Homeomorph.apply_symm_apply]
    let a' : C(Boundary n, E) := a.hom.comp ⟨d.symm, d.symm.continuous⟩
    let b' : C(Cube n, B) := b.hom.comp ⟨e.symm, e.symm.continuous⟩
    have hab (t : Boundary n) : p (a' t) = b' t := by
      change p (a (d.symm t)) = b (e.symm t.val)
      rw [hpair_symm]
      exact ConcreteCategory.congr_hom sq.w (d.symm t)
    obtain ⟨c, hc, he⟩ := hp n a' b' hab
    refine ⟨TopCat.ofHom (c.comp ⟨e, e.continuous⟩), ?_, ?_⟩
    · ext x
      change c (e (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})) x)) = a x
      rw [hpair]
      have h := hc (d x)
      change c (d x).val = a (d.symm (d x)) at h
      simpa only [Homeomorph.symm_apply_apply] using h
    · ext x
      change p (c (e x)) = b x
      have h := ContinuousMap.congr_fun he (e x)
      change p (c (e x)) = b (e.symm (e x)) at h
      simpa only [Homeomorph.symm_apply_apply] using h

end Topology.CubicalSubdivision

namespace Topology.MappingPath

universe u

/-- A weak equivalence supplies lifting of its original mapping-path endpoint
against each actual realized simplex boundary. -/
theorem endpoint_hasLiftingProperty_realizationBoundary_of_isWeakHomotopyEquivalence
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsWeakHomotopyEquivalence f) (n : ℕ) :
    HasLiftingProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
      (TopCat.ofHom (endpoint f)) :=
  CubicalSubdivision.BoundaryLifting.hasLiftingProperty_realizationBoundary
    ((isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting f).mp hf) n

end Topology.MappingPath
