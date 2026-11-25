/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.Topology.Homotopy.CubeBoundary
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith

/-!
# Exact extension of a simplex-valued cube boundary

An explicit continuous retraction of finite nonnegative coordinate vectors onto the standard
simplex turns the nonnegative real Tietze theorem into an exact simplex extension theorem.
No extension or compatibility of particular boundary faces is assumed by this theorem.

Adapted from `Quillen/Topology/Realization/SimplexCubeExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with Mathlib's actual cube boundary.
-/

@[expose] public noncomputable section

open Convexity
open scoped Topology unitInterval

namespace Topology.SimplexCubeExtension

variable {ι : Type*} [Fintype ι]

/-- Total mass of a nonnegative coordinate vector. -/
def mass (a : ι → NNReal) : ℝ := ∑ i, (a i : ℝ)

/-- Extra mass needed to make the total at least one. -/
def deficit (a : ι → NNReal) : ℝ := max 0 (1 - mass a)

/-- The normalization divisor is everywhere at least one. -/
def denominator (a : ι → NNReal) : ℝ := mass a + deficit a

theorem denominator_pos (a : ι → NNReal) : 0 < denominator a := by
  have h := le_max_right (0 : ℝ) (1 - mass a)
  dsimp [denominator, deficit]
  linarith

open Classical in
/-- Add missing mass at a fixed vertex and then normalize. -/
def retract (v : ι) (a : ι → NNReal) : StdSimplex ℝ ι where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ ((a i : ℝ) + if i = v then deficit a else 0) / denominator a)
  nonneg i := by
    change 0 ≤ ((a i : ℝ) + if i = v then deficit a else 0) / denominator a
    apply div_nonneg _ (denominator_pos a).le
    apply add_nonneg (a i).coe_nonneg
    split_ifs
    · exact le_max_left _ _
    · rfl
  total := by
    classical
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i, ((a i : ℝ) + if i = v then deficit a else 0) / denominator a) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have hsum : (∑ i : ι, if i = v then deficit a else 0) = deficit a := by simp
    rw [hsum]
    exact div_self (denominator_pos a).ne'

open Classical in
@[simp] theorem retract_weights (v : ι) (a : ι → NNReal) (i : ι) :
    (retract v a).weights i =
      ((a i : ℝ) + if i = v then deficit a else 0) / denominator a := by
  simp [retract]

theorem continuous_mass : Continuous (mass : (ι → NNReal) → ℝ) := by
  unfold mass
  fun_prop

theorem continuous_deficit : Continuous (deficit : (ι → NNReal) → ℝ) :=
  continuous_const.max (continuous_const.sub continuous_mass)

theorem continuous_denominator : Continuous (denominator : (ι → NNReal) → ℝ) :=
  continuous_mass.add continuous_deficit

theorem continuous_retract (v : ι) : Continuous (retract v : (ι → NNReal) → StdSimplex ℝ ι) := by
  classical
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, retract_weights]
  have h : Continuous (fun a : ι → NNReal ↦ if i = v then deficit a else 0) := by
    by_cases hi : i = v
    · simpa [hi] using (continuous_deficit (ι := ι))
    · simp only [hi, ↓reduceIte]
      exact continuous_const
  exact ((continuous_subtype_val.comp (continuous_apply i)).add h).div
    continuous_denominator (fun a ↦ (denominator_pos a).ne')

/-- Barycentric coordinates viewed as nonnegative real numbers. -/
def coordinates (w : StdSimplex ℝ ι) : ι → NNReal :=
  fun i ↦ ⟨w.weights i, w.weights_nonneg i⟩

omit [Fintype ι] in
theorem continuous_coordinates : Continuous (coordinates : StdSimplex ℝ ι → ι → NNReal) := by
  apply continuous_pi
  intro i
  exact (StdSimplex.continuous_weights_apply ℝ i).subtype_mk _

@[simp] theorem mass_coordinates (w : StdSimplex ℝ ι) : mass (coordinates w) = 1 :=
  w.total_of_fintype

@[simp] theorem retract_coordinates (v : ι) (w : StdSimplex ℝ ι) :
    retract v (coordinates w) = w := by
  apply StdSimplex.ext
  ext i
  simp [deficit, denominator, coordinates]
  rfl

/-- Every continuous map from a closed subset of a normal space to a finite real standard
simplex extends with exact restriction. The vertex exists explicitly; no filler is an input. -/
theorem exists_closed_extension {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {κ : Type*} [Finite κ] {s : Set X} (v : κ) (hs : IsClosed s)
    (f : C(s, StdSimplex ℝ κ)) :
    ∃ E : C(X, StdSimplex ℝ κ), E.restrict s = f := by
  let := Fintype.ofFinite κ
  let q : C(StdSimplex ℝ κ, κ → NNReal) := ⟨coordinates, continuous_coordinates⟩
  obtain ⟨g, hg⟩ := (q.comp f).exists_restrict_eq hs
  refine ⟨⟨fun x ↦ retract v (g x), (continuous_retract v).comp g.continuous⟩, ?_⟩
  apply ContinuousMap.ext
  intro x
  change retract v (g x) = f x
  have hx : g x = coordinates (f x) := congrArg (fun h : C(s, κ → NNReal) ↦ h x) hg
  rw [hx, retract_coordinates]

/-- The parameter cube, with the product topology of three unit intervals. -/
abbrev Cube := Fin 3 → I

/-- Mathlib's boundary of the three-dimensional parameter cube. -/
abbrev boundary : Set Cube := _root_.Cube.boundary (Fin 3)

/-- Exact continuous extension of the whole cube boundary into every finite standard simplex,
including the singleton simplex when `N = 0`. -/
theorem exists_cube_extension (N : ℕ) (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) :
    ∃ E : C(Cube, StdSimplex ℝ (Fin (N + 1))), E.restrict boundary = f :=
  exists_closed_extension 0 (_root_.Cube.isClosed_boundary (Fin 3)) f

/-- A chosen exact extension; the choices are the nonnegative Tietze extensions. -/
def cubeExtension (N : ℕ) (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) :
    C(Cube, StdSimplex ℝ (Fin (N + 1))) :=
  (exists_cube_extension N f).choose

@[simp] theorem cubeExtension_restrict (N : ℕ)
    (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) :
    (cubeExtension N f).restrict boundary = f :=
  (exists_cube_extension N f).choose_spec

/-- Equality is pointwise on the entire boundary, not merely at its vertices or edges. -/
@[simp] theorem cubeExtension_boundary (N : ℕ)
    (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) (x : boundary) :
    cubeExtension N f x = f x :=
  congrArg (fun h : C(boundary, StdSimplex ℝ (Fin (N + 1))) ↦ h x)
    (cubeExtension_restrict N f)

/-- Every point of an entire zero coordinate face retains its prescribed value. -/
theorem cubeExtension_face_zero (N : ℕ)
    (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) (i : Fin 3) (x : Cube) (hx : x i = 0) :
    cubeExtension N f x = f ⟨x, i, Or.inl hx⟩ :=
  cubeExtension_boundary N f ⟨x, i, Or.inl hx⟩

/-- Every point of an entire one coordinate face retains its prescribed value. -/
theorem cubeExtension_face_one (N : ℕ)
    (f : C(boundary, StdSimplex ℝ (Fin (N + 1)))) (i : Fin 3) (x : Cube) (hx : x i = 1) :
    cubeExtension N f x = f ⟨x, i, Or.inr hx⟩ :=
  cubeExtension_boundary N f ⟨x, i, Or.inr hx⟩

/-- The continuous-function formulation has exactly the closed-boundary map as input. -/
theorem exists_cube_extension_of_continuous (N : ℕ)
    (f : boundary → StdSimplex ℝ (Fin (N + 1))) (hf : Continuous f) :
    ∃ E : Cube → StdSimplex ℝ (Fin (N + 1)), Continuous E ∧
      ∀ x : boundary, E x = f x := by
  refine ⟨cubeExtension N ⟨f, hf⟩, (cubeExtension N ⟨f, hf⟩).continuous, ?_⟩
  exact cubeExtension_boundary N ⟨f, hf⟩

end Topology.SimplexCubeExtension
