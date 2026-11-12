/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalEquiconnection
public import Colib.Topology.Realization.SimplexBoundary.Charts
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# A genuine continuous connector extension over a simplex cone

The compact quotient I × Δ[n] → Δ[n+1] collapses exactly the height-one
fiber. The endpoint law makes the connector map constant there, so it
descends continuously even at the apex. This is the inductive extension
step, not an assumption that a complete coherent realization map exists.
-/

open Topology Convexity.StdSimplex

/-! Implementation source: `Quillen/Topology/Realization/ConnectorSimplexCone.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
open Convexity
open scoped Topology unitInterval
universe u
namespace Topology.NumerableConnectorCover

/-- The actual compact simplex-cone parameter map; height one is the apex. -/
def simplexConeParameter (n : ℕ) :
    C(I × StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 2))) :=
  ⟨fun p ↦ simplexBoundaryCone p.1 p.2, continuous_simplexBoundaryCone n⟩

/-- Every simplex point has cone coordinates, including the collapsed apex. -/
theorem simplexConeParameter_surjective (n : ℕ) :
    Function.Surjective (simplexConeParameter n) := by
  intro x
  by_cases hx : x.weights 0 < 1
  · exact ⟨(⟨x.weights 0, x.weights_nonneg 0, x.weights_apply_le_one 0⟩,
      simplexBoundaryTail x hx), simplexBoundaryCone_tail x hx⟩
  · have hxone : x.weights 0 = 1 := le_antisymm (x.weights_apply_le_one 0) (le_of_not_gt hx)
    have hz (i : Fin (n + 1)) : x.weights i.succ = 0 := by
      have hle : x.weights i.succ ≤ ∑ j : Fin (n + 1), x.weights j.succ :=
        Finset.single_le_sum (fun j _ ↦ x.weights_nonneg j.succ) (Finset.mem_univ i)
      rw [sum_simplexBoundary_tail, hxone, sub_self] at hle
      exact le_antisymm hle (x.weights_nonneg i.succ)
    refine ⟨(1, StdSimplex.single 0), ?_⟩
    apply StdSimplex.ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hxone.symm
    · change (1 - (1 : ℝ)) * (StdSimplex.single 0).weights j = x.weights j.succ
      simp only [sub_self, zero_mul, hz]

/-- Cone fibers are singleton except for the height-one apex fiber. -/
theorem simplexConeParameter_fiber {n : ℕ}
    {p q : I × StdSimplex ℝ (Fin (n + 1))}
    (h : simplexConeParameter n p = simplexConeParameter n q) :
    p.1 = q.1 ∧ (p.1 = 1 ∨ p.2 = q.2) := by
  have ht : p.1 = q.1 := Subtype.ext (congrArg (fun x ↦ x.weights 0) h)
  refine ⟨ht, ?_⟩
  by_cases hp : p.1 = 1
  · exact Or.inl hp
  · right
    have hne : 1 - (p.1 : ℝ) ≠ 0 := by
      intro heq
      apply hp
      apply Subtype.ext
      change (p.1 : ℝ) = 1
      linarith
    apply StdSimplex.ext
    ext i
    have hi := congrArg (fun x ↦ x.weights i.succ) h
    change (1 - (p.1 : ℝ)) * p.2.weights i = (1 - (q.1 : ℝ)) * q.2.weights i at hi
    rw [← ht] at hi
    exact mul_left_cancel₀ hne hi

/-- The compact cone parameter map is a quotient for the genuine finite-simplex topology. -/
theorem simplexConeParameter_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (simplexConeParameter n) := by
  let : T2Space (StdSimplex ℝ (Fin (n + 2))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t2Space
  exact .of_surjective_continuous (simplexConeParameter_surjective n)
    (simplexConeParameter n).continuous

variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A) {n : ℕ}

/-- The continuous connector formula before quotienting the cone apex. -/
def connectorConeFormula (a : A) (f : C(StdSimplex ℝ (Fin (n + 1)), A))
    (h : ∀ y, (a, f y) ∈ E.domain) : C(I × StdSimplex ℝ (Fin (n + 1)), A) where
  toFun p := E.connector (⟨(a, f p.2), h p.2⟩, unitInterval.symm p.1)
  continuous_toFun := E.connector.continuous.comp
    ((continuous_const.prodMk (f.continuous.comp continuous_snd)).subtype_mk _ |>.prodMk
      (unitInterval.continuous_symm.comp continuous_fst))

/-- The endpoint law is exactly the compatibility required on collapsed cone fibers. -/
theorem connectorConeFormula_factors (a : A) (f : C(StdSimplex ℝ (Fin (n + 1)), A))
    (h : ∀ y, (a, f y) ∈ E.domain) :
    Function.FactorsThrough (connectorConeFormula E a f h) (simplexConeParameter n) := by
  intro p q hpq
  obtain ⟨ht, hp | hy⟩ := simplexConeParameter_fiber hpq
  · have hq : q.1 = 1 := ht.symm.trans hp
    change E.connector (⟨(a, f p.2), h p.2⟩, unitInterval.symm p.1) =
      E.connector (⟨(a, f q.2), h q.2⟩, unitInterval.symm q.1)
    simp only [hp, hq, unitInterval.symm_one, E.connector_zero]
  · exact congrArg (connectorConeFormula E a f h) (Prod.ext ht hy)

/-- An actual extension to the whole simplex, continuous at its cone vertex. -/
def connectorCone (a : A) (f : C(StdSimplex ℝ (Fin (n + 1)), A))
    (h : ∀ y, (a, f y) ∈ E.domain) : C(StdSimplex ℝ (Fin (n + 2)), A) :=
  (simplexConeParameter_isQuotientMap n).lift (connectorConeFormula E a f h)
    (connectorConeFormula_factors E a f h)

/-- Exact evaluation on every cone coordinate, including both endpoints. -/
theorem connectorCone_apply (a : A) (f : C(StdSimplex ℝ (Fin (n + 1)), A))
    (h : ∀ y, (a, f y) ∈ E.domain) (t : I) (y : StdSimplex ℝ (Fin (n + 1))) :
    connectorCone E a f h (simplexBoundaryCone t y) =
      E.connector (⟨(a, f y), h y⟩, unitInterval.symm t) := by
  have heq := (simplexConeParameter_isQuotientMap n).lift_comp
    (connectorConeFormula E a f h) (connectorConeFormula_factors E a f h)
  exact congrArg (fun g : C(I × StdSimplex ℝ (Fin (n + 1)), A) ↦ g (t, y)) heq

/-- A common convex carrier is preserved on the entire cone extension. -/
theorem connectorCone_mem {V : Set A} (hV : E.IsConvex V) (a : A) (ha : a ∈ V)
    (f : C(StdSimplex ℝ (Fin (n + 1)), A)) (hf : ∀ y, f y ∈ V)
    (x : StdSimplex ℝ (Fin (n + 2))) :
    connectorCone E a f (fun y ↦ hV.pair_mem ha (hf y)) x ∈ V := by
  obtain ⟨⟨t, y⟩, rfl⟩ := simplexConeParameter_surjective n x
  change connectorCone E a f _ (simplexBoundaryCone t y) ∈ V
  rw [connectorCone_apply]
  exact hV.connector_mem ha (hf y) (unitInterval.symm t)

end Topology.NumerableConnectorCover
