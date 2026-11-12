/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.OrderedConnectorInterpolation
public import Mathlib.Data.Fin.SuccPred

/-!
# Zero-coordinate faces of ordered connector interpolation

The cone's coefficient algebra is independent of the target connector.
Face compatibility follows by dimension induction from the two endpoint
laws and exact cone naturality. No binary associativity is used.
-/

open Topology Convexity.StdSimplex

/-! Implementation source: `Quillen/Topology/Realization/ConnectorSimplexFaces.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Topology unitInterval
universe u
namespace Topology.NumerableConnectorCover

/-- The cone weights split as the first vertex mass and the shifted tail mass. -/
theorem simplexCone_weights {n : ℕ} (t : I) (x : StdSimplex ℝ (Fin (n + 1))) :
    (simplexBoundaryCone t x).weights =
      Finsupp.single 0 (t : ℝ) + (1 - (t : ℝ)) • x.weights.mapDomain Fin.succ := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [simplexBoundaryCone_weights_zero, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨j, hj⟩
      exact Fin.succ_ne_zero j hj
  · simp [Finsupp.mapDomain_apply_of_injective (Fin.succ_injective _)]

/-- Height zero is exactly the increasing opposite-face inclusion. -/
theorem simplexCone_zero {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryCone 0 x = x.map Fin.succ := by
  apply StdSimplex.ext
  rw [simplexCone_weights]
  simp

/-- Height one is exactly the first simplex vertex. -/
theorem simplexCone_one {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryCone 1 x = StdSimplex.single 0 := by
  apply StdSimplex.ext
  rw [simplexCone_weights]
  simp

/-- Mapping the tail commutes with coning and aggregates weights by the actual pushforward. -/
theorem simplexCone_map_tail {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (t : I) (x : StdSimplex ℝ (Fin (n + 1))) :
    (simplexBoundaryCone t x).map (Fin.cases 0 (fun i ↦ (f i).succ)) =
      simplexBoundaryCone t (x.map f) := by
  apply StdSimplex.ext
  rw [StdSimplex.weights_map, simplexCone_weights, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp,
    simplexCone_weights, StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
  rfl

/-- Inserting a zero away from the first coordinate commutes with the cone parameter. -/
theorem simplexCone_map_succAbove {n : ℕ} (i : Fin (n + 2))
    (t : I) (x : StdSimplex ℝ (Fin (n + 1))) :
    (simplexBoundaryCone t x).map i.succ.succAbove =
      simplexBoundaryCone t (x.map i.succAbove) := by
  have h : i.succ.succAbove = Fin.cases 0 (fun j ↦ (i.succAbove j).succ) := by
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  rw [h]
  exact simplexCone_map_tail i.succAbove t x

variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Every elementary increasing face of the recursively constructed map is the
recursively constructed map of that face's vertex list. -/
theorem interpolate_face : ∀ (n : ℕ) (v : Fin (n + 2) → A)
    (hv : AdmissibleVertices E v) (i : Fin (n + 2)) (x : StdSimplex ℝ (Fin (n + 1))),
    interpolate E v hv (x.map i.succAbove) =
      interpolate E (v ∘ i.succAbove) (hv.comp i.succAbove) x := by
  intro n
  induction n with
  | zero =>
    intro v hv i x
    have hx : x = StdSimplex.single 0 := by
      apply StdSimplex.ext
      ext j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp
    subst x
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.succAbove_zero, ← simplexCone_zero] using
        interpolate_cone_zero E v hv (StdSimplex.single 0)
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [StdSimplex.map_single]
      have hc := interpolate_cone_one E v hv (StdSimplex.single 0)
      rw [simplexCone_one] at hc
      simpa using hc
  | succ n ih =>
    intro v hv i x
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.succAbove_zero, ← simplexCone_zero] using interpolate_cone_zero E v hv x
    · obtain ⟨⟨t, y⟩, rfl⟩ := simplexConeParameter_surjective n x
      change interpolate E v hv ((simplexBoundaryCone t y).map j.succ.succAbove) =
        interpolate E (v ∘ j.succ.succAbove) _ (simplexBoundaryCone t y)
      rw [simplexCone_map_succAbove, interpolate_cone, interpolate_cone]
      have ht := ih (v ∘ Fin.succ) (hv.comp Fin.succ) j y
      have hhead : (v ∘ j.succ.succAbove) 0 = v 0 := by simp
      have htail : (v ∘ j.succ.succAbove) ∘ Fin.succ =
          (v ∘ Fin.succ) ∘ j.succAbove := by
        funext k
        simp [Function.comp_def]
      simp only [htail, hhead]
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext rfl ht
      · rfl

end Topology.NumerableConnectorCover
