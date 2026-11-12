/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ConnectorSimplexCone

/-!
# Constructed finite ordered connector interpolation

The interpolation is recursively constructed from the vertex list using the
actual compact-cone extension. Its only geometric hypothesis is that the
vertices lie in some connector-convex set. It preserves every such carrier,
not just one selected witness. No interpolation map or extension is assumed.
The list order is retained; no associativity of the connector is asserted.
-/

open Topology Convexity.StdSimplex

/-! Implementation source: `Quillen/Topology/Realization/OrderedConnectorInterpolation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Topology unitInterval
universe u v
namespace Topology.NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- A family of target vertices lies in one actual connector-convex carrier. -/
def AdmissibleVertices {ι : Type v} (v : ι → A) : Prop :=
  ∃ V, E.IsConvex V ∧ ∀ i, v i ∈ V

variable {E} in
/-- Restricting or repeating indices preserves the geometric carrier condition. -/
theorem AdmissibleVertices.comp {ι κ : Type*} {v : ι → A}
    (hv : AdmissibleVertices E v) (f : κ → ι) : AdmissibleVertices E (v ∘ f) := by
  obtain ⟨V, hV, hv⟩ := hv
  exact ⟨V, hV, fun i ↦ hv (f i)⟩

/-- Inductively constructed maps together with their universal carrier invariant. -/
def interpolateWithCarrier : (n : ℕ) → (v : Fin (n + 1) → A) →
    AdmissibleVertices E v →
    {f : C(StdSimplex ℝ (Fin (n + 1)), A) //
      ∀ V, E.IsConvex V → (∀ i, v i ∈ V) → ∀ x, f x ∈ V}
  | 0, v, _ => ⟨ContinuousMap.const _ (v 0), by
      intro V _hV hv _x
      exact hv 0⟩
  | n + 1, v, hv => by
      let f := interpolateWithCarrier n (v ∘ Fin.succ) (hv.comp Fin.succ)
      have hp : ∀ y, (v 0, f.1 y) ∈ E.domain := by
        intro y
        obtain ⟨V, hV, hv⟩ := hv
        exact hV.pair_mem (hv 0) (f.2 V hV (fun i ↦ hv i.succ) y)
      refine ⟨connectorCone E (v 0) f.1 hp, ?_⟩
      intro V hV hv x
      exact connectorCone_mem E hV (v 0) (hv 0) f.1
        (f.2 V hV (fun i ↦ hv i.succ)) x

/-- The actual ordered continuous interpolation on a finite simplex. -/
def interpolate {n : ℕ} (v : Fin (n + 1) → A) (hv : AdmissibleVertices E v) :
    C(StdSimplex ℝ (Fin (n + 1)), A) := (interpolateWithCarrier E n v hv).1

/-- Every connector-convex set containing the vertices contains the entire interpolation. -/
theorem interpolate_mem {n : ℕ} (v : Fin (n + 1) → A) (hv : AdmissibleVertices E v)
    {V : Set A} (hV : E.IsConvex V) (hverts : ∀ i, v i ∈ V)
    (x : StdSimplex ℝ (Fin (n + 1))) : interpolate E v hv x ∈ V :=
  (interpolateWithCarrier E n v hv).2 V hV hverts x

/-- The zero-dimensional map has exactly its specified vertex value. -/
@[simp] theorem interpolate_zero (v : Fin 1 → A) (hv : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin 1)) : interpolate E v hv x = v 0 := rfl

/-- The recursive connector pair is geometrically defined for every tail point. -/
theorem interpolate_head_pair_mem {n : ℕ} (v : Fin (n + 2) → A)
    (hv : AdmissibleVertices E v) (y : StdSimplex ℝ (Fin (n + 1))) :
    (v 0, interpolate E (v ∘ Fin.succ) (hv.comp Fin.succ) y) ∈ E.domain := by
  obtain ⟨V, hV, hverts⟩ := hv
  exact hV.pair_mem (hverts 0)
    (interpolate_mem E (v ∘ Fin.succ) (by exact ⟨V, hV, fun i ↦ hverts i.succ⟩)
      hV (fun i ↦ hverts i.succ) y)

/-- Exact recursive evaluation, including zero head weight and the collapsed apex. -/
theorem interpolate_cone {n : ℕ} (v : Fin (n + 2) → A)
    (hv : AdmissibleVertices E v) (t : I) (y : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v hv (simplexBoundaryCone t y) =
      E.connector (⟨(v 0, interpolate E (v ∘ Fin.succ) (hv.comp Fin.succ) y),
        interpolate_head_pair_mem E v hv y⟩, unitInterval.symm t) := by
  exact connectorCone_apply E (v 0)
    (interpolate E (v ∘ Fin.succ) (hv.comp Fin.succ)) _ t y

/-- Deleting the first zero coordinate gives the entire original tail interpolation. -/
theorem interpolate_cone_zero {n : ℕ} (v : Fin (n + 2) → A)
    (hv : AdmissibleVertices E v) (y : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v hv (simplexBoundaryCone 0 y) =
      interpolate E (v ∘ Fin.succ) (hv.comp Fin.succ) y := by
  rw [interpolate_cone]
  simp only [unitInterval.symm_zero, E.connector_one]

/-- The apex value is independent of every tail coordinate. -/
theorem interpolate_cone_one {n : ℕ} (v : Fin (n + 2) → A)
    (hv : AdmissibleVertices E v) (y : StdSimplex ℝ (Fin (n + 1))) :
    interpolate E v hv (simplexBoundaryCone 1 y) = v 0 := by
  rw [interpolate_cone]
  simp only [unitInterval.symm_one, E.connector_zero]

end Topology.NumerableConnectorCover
