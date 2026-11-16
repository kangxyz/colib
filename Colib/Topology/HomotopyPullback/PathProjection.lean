/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Basic

/-!
# The original two-endpoint path projection

The target is the existing `HomotopyPullback p p`, with its inherited product
and compact-open topology. The path projection records both original endpoints
and the entire projected base path. A lift of a prescribed homotopy into this
path space uncurries to a jointly continuous homotopy with exactly those endpoints
and that original base homotopy.

Adapted from `Quillen/Topology/HomotopyPullback/PathProjection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyPullback
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))

/-- Record the final endpoint, initial endpoint, and projected original path. -/
def pathProjection : C(C(I, E), HomotopyPullback p p) where
  toFun γ := ⟨(γ 1, γ 0, p.comp γ), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : C(I, E) × I ↦ p (z.1 z.2))
        fun_prop

@[simp] theorem pathProjection_start (γ : C(I, E)) :
    sourceProjection p p (pathProjection p γ) = γ 0 := rfl

@[simp] theorem pathProjection_finish (γ : C(I, E)) :
    baseProjection p p (pathProjection p γ) = γ 1 := rfl

@[simp] theorem pathProjection_path (γ : C(I, E)) (t : I) :
    (pathProjection p γ).val.2.2 t = p (γ t) := rfl

/-- A prescribed base homotopy, together with its two source endpoint maps,
defines a map into the canonical homotopy pullback. -/
def homotopyTarget {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) :
    C(X, HomotopyPullback p p) where
  toFun x := ⟨(a₁ x, a₀ x, ⟨fun t ↦ H (t, x), by fun_prop⟩),
    H.apply_zero x, H.apply_one x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk a₁.continuous
    apply Continuous.prodMk a₀.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : X × I ↦ H (z.2, z.1))
    exact H.continuous.comp continuous_swap

@[simp] theorem homotopyTarget_start {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) (x : X) :
    sourceProjection p p (homotopyTarget p a₀ a₁ H x) = a₀ x := rfl

@[simp] theorem homotopyTarget_finish {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) (x : X) :
    baseProjection p p (homotopyTarget p a₀ a₁ H x) = a₁ x := rfl

@[simp] theorem homotopyTarget_path {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) (x : X) (t : I) :
    (homotopyTarget p a₀ a₁ H x).val.2.2 t = H (t, x) := rfl

/-- Uncurry an actual path-space lift. Continuity is joint in time and the
parameter, by the compact-open evaluation theorem for the interval. -/
def homotopyOfPathProjectionLift {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁))
    (l : C(X, C(I, E))) (hl : (pathProjection p).comp l = homotopyTarget p a₀ a₁ H) :
    a₀.Homotopy a₁ where
  toFun z := l z.2 z.1
  continuous_toFun := by fun_prop
  map_zero_left x := congrArg (fun z : HomotopyPullback p p ↦ z.val.2.1)
    (ContinuousMap.congr_fun hl x)
  map_one_left x := congrArg (fun z : HomotopyPullback p p ↦ z.val.1)
    (ContinuousMap.congr_fun hl x)

/-- The uncurried lift projects to the entire prescribed base homotopy pointwise. -/
theorem homotopyOfPathProjectionLift_project {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁))
    (l : C(X, C(I, E))) (hl : (pathProjection p).comp l = homotopyTarget p a₀ a₁ H)
    (t : I) (x : X) :
    p (homotopyOfPathProjectionLift p a₀ a₁ H l hl (t, x)) = H (t, x) :=
  congrArg (fun z : HomotopyPullback p p ↦ z.val.2.2 t) (ContinuousMap.congr_fun hl x)

end Topology.HomotopyPullback
