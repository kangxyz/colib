/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.ContinuousOn

/-!
# Discrete labels and the actual disjoint union of path components

A continuous discrete label whose fibers are the specified path components
gives a homeomorphism from their topological disjoint union to the original
space. The forward map is exactly the component inclusions. Openness can also
be transported through actual domination maps and their displayed homotopy.
No discreteness of path components of an arbitrary space is assumed.
-/

open Topology

/-! Implementation source: `Quillen/Topology/HomotopyEquiv/ComponentSigma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology
universe u v w
namespace Topology

variable {X : Type u} {Y : Type v} {A : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]

/-- Actual domination reflects path components, using the two endpoint tracks. -/
theorem pathComponent_eq_preimage_of_domination (a : C(X, Y)) (b : C(Y, X))
    (H : (b.comp a).Homotopy (ContinuousMap.id X)) (x : X) :
    pathComponent x = a ⁻¹' pathComponent (a x) := by
  ext z
  constructor
  · intro h
    exact h.map a.continuous
  · intro h
    exact (show Joined x (b (a x)) from ⟨(H.evalAt x).symm⟩).trans
      ((h.map b.continuous).trans ⟨H.evalAt z⟩)

/-- Domination by a space with open path components supplies the required openness. -/
theorem isOpen_pathComponent_of_domination (a : C(X, Y)) (b : C(Y, X))
    (H : (b.comp a).Homotopy (ContinuousMap.id X))
    (hY : ∀ y : Y, IsOpen (pathComponent y)) (x : X) :
    IsOpen (pathComponent x) := by
  rw [pathComponent_eq_preimage_of_domination a b H x]
  exact (hY (a x)).preimage a.continuous

variable [DiscreteTopology A]

/-- A set-theoretic component classifier is continuous when its actual components are open. -/
theorem continuous_componentLabel_of_isOpen (label : X → A) (r : A → X)
    (h : ∀ a z, label z = a ↔ Joined (r a) z)
    (ho : ∀ a, IsOpen (pathComponent (r a))) : Continuous label := by
  apply continuous_discrete_rng.mpr
  intro a
  have he : label ⁻¹' {a} = pathComponent (r a) := by
    ext z
    exact h a z
  rw [he]
  exact ho a

/-- A discrete product is the topological disjoint union of its identical fibers. -/
def discreteProductSigmaHomeomorph (A : Type w) (X : Type u)
    [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace X] :
    A × X ≃ₜ Σ _ : A, X where
  toEquiv := (Equiv.sigmaEquivProd A X).symm
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun a ↦ by
    change Continuous (fun z : X ↦ (⟨a, z⟩ : Σ _ : A, X))
    exact continuous_sigmaMk (σ := fun _ : A ↦ X) (i := a)
  continuous_invFun := continuous_sigma fun a ↦ by
    change Continuous (fun z : X ↦ (a, z))
    exact continuous_const.prodMk continuous_id

/-- Continuous discrete labels identify the whole space with its actual path-component sum. -/
def componentSigmaHomeomorph (label : C(X, A)) (r : A → X)
    (h : ∀ a z, label z = a ↔ Joined (r a) z) :
    (Σ a : A, pathComponent (r a)) ≃ₜ X := by
  let f : (Σ a : A, pathComponent (r a)) → X := fun z ↦ z.2.val
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, z⟩ ⟨b, w⟩ he
      have hab : a = b := ((h a z.val).mpr z.property).symm.trans
        ((congrArg label he).trans ((h b w.val).mpr w.property))
      subst b
      exact congrArg (Sigma.mk a) (Subtype.ext he)
    · intro z
      exact ⟨⟨label z, ⟨z, (h (label z) z).mp rfl⟩⟩, rfl⟩
  refine (Equiv.ofBijective f hf).toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val) ?_
  apply isOpenMap_sigma.mpr
  intro a
  have he : pathComponent (r a) = label ⁻¹' {a} := by
    ext z
    exact (h a z).symm
  have ho : IsOpen (pathComponent (r a)) := by
    rw [he]
    exact (isOpen_discrete {a}).preimage label.continuous
  exact ho.isOpenMap_subtype_val

/-- The component-sum homeomorphism preserves the original underlying points exactly. -/
@[simp]
theorem componentSigmaHomeomorph_apply (label : C(X, A)) (r : A → X)
    (h : ∀ a z, label z = a ↔ Joined (r a) z)
    (a : A) (z : pathComponent (r a)) :
    componentSigmaHomeomorph label r h ⟨a, z⟩ = z.val := rfl

end Topology
