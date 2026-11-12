/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalEquiconnection
public import Mathlib.Topology.Path

/-!
# Local connectors on the original compact-open based loop space

A diagonal-fixed local connector acts pointwise on literal based paths. The
pairwise domain is open by compactness of the interval and the compact-open
range-subset theorem. The whole-diagonal identity fixes both path endpoints.
All continuity statements use the existing Path topology.
-/

open Topology

/-! Implementation source: `Quillen/Topology/LocalEquiconnection/Loops.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u
namespace Topology.LocalEquiconnection

variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A) (p : A)

/-- Pair two original loops pointwise as one actual compact-open continuous map. -/
def pairedLoops : C(Path p p × Path p p, C(I, A × A)) where
  toFun z := ⟨fun t ↦ (z.1 t, z.2 t), by fun_prop⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (Path p p × Path p p) × I ↦ (z.1.1 z.2, z.1.2 z.2))
    fun_prop

/-- The domain requires a permitted pair at every original loop time. -/
def loopDomain : Set (Path p p × Path p p) := {z | ∀ t : I, (z.1 t, z.2 t) ∈ E.domain}

/-- Compactness of the interval makes the pointwise domain open in the original Path product. -/
theorem isOpen_loopDomain : IsOpen (E.loopDomain p) := by
  have h := (ContinuousMap.isOpen_setOfPred_range_subset E.isOpen_domain).preimage
    (pairedLoops p).continuous
  simpa only [Set.preimage_ofPred_eq, Set.range_subset_iff, pairedLoops,
    ContinuousMap.coe_mk, loopDomain] using h

/-- Every whole loop lies on the pointwise diagonal of the permitted domain. -/
theorem loopDomain_diagonal (γ : Path p p) : (γ, γ) ∈ E.loopDomain p :=
  fun t ↦ E.diagonal_mem (γ t)

/-- The actual pointwise connector, with the original loop endpoint equations. -/
def loopConnector : C(E.loopDomain p × I, Path p p) where
  toFun z := {
    toFun s := E.connector (⟨(z.1.1.1 s, z.1.1.2 s), z.1.2 s⟩, z.2)
    continuous_toFun := by
      apply E.connector.continuous.comp
      fun_prop
    source' := by
      simpa only [Path.source] using E.connector_diagonal p z.2
    target' := by
      simpa only [Path.target] using E.connector_diagonal p z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (E.loopDomain p × I) × I ↦
      E.connector (⟨(z.1.1.1.1 z.2, z.1.1.1.2 z.2), z.1.1.2 z.2⟩, z.1.2))
    apply E.connector.continuous.comp
    fun_prop

/-- Evaluation retains the pointwise connector exactly. -/
theorem loopConnector_apply (z : E.loopDomain p) (t s : I) :
    E.loopConnector p (z, t) s = E.connector (⟨(z.1.1 s, z.1.2 s), z.2 s⟩, t) := rfl

@[simp]
theorem loopConnector_zero (z : E.loopDomain p) : E.loopConnector p (z, 0) = z.1.1 := by
  apply Path.ext
  funext s
  exact E.connector_zero ⟨(z.1.1 s, z.1.2 s), z.2 s⟩

@[simp]
theorem loopConnector_one (z : E.loopDomain p) : E.loopConnector p (z, 1) = z.1.2 := by
  apply Path.ext
  funext s
  exact E.connector_one ⟨(z.1.1 s, z.1.2 s), z.2 s⟩

/-- The entire original loop is retained on the diagonal for every connector time. -/
@[simp]
theorem loopConnector_diagonal (γ : Path p p) (t : I) :
    E.loopConnector p (⟨(γ, γ), E.loopDomain_diagonal p γ⟩, t) = γ := by
  apply Path.ext
  funext s
  exact E.connector_diagonal (γ s) t

/-- A genuine local equiconnection of the unchanged compact-open based loop space. -/
def loops : LocalEquiconnection (Path p p) where
  domain := E.loopDomain p
  isOpen_domain := E.isOpen_loopDomain p
  diagonal_mem := E.loopDomain_diagonal p
  connector := E.loopConnector p
  connector_zero := E.loopConnector_zero p
  connector_one := E.loopConnector_one p
  connector_diagonal := E.loopConnector_diagonal p

end Topology.LocalEquiconnection
