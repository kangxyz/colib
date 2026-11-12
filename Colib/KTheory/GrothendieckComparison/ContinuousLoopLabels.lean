/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.KTheory.GrothendieckComparison.LoopComponents
public import Colib.Topology.ClassifyingSpace.OpenLoopComponents
public import Mathlib.Topology.WithTopology

/-!
# The actual continuous discrete original Q-loop K₀ classifier

Only the topology of the label copy is changed: its underlying value is the
preexisting loopComponentsKZeroEquiv applied to the original loop component.
The original Q-loop topology is unchanged. The proven open components imply
continuity, and fibers are exactly the original path components.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/GrothendieckComparison/ContinuousLoopLabels.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace CategoryTheory.ExactCategory.ExactStructure
open Topology CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A discrete copy of unchanged homotopical Quillen K₀, with explicit forgetful projection. -/
abbrev DiscreteKZero := WithDiscreteTopology (E.K 0)

/-- The original loop-component class, placed in its discrete copy without relabeling. -/
def loopKZeroLabel (γ : Path E.kBasepoint E.kBasepoint) : E.DiscreteKZero :=
  WithTopology.toTopology ⊥ (E.loopComponentsKZeroEquiv (ZerothHomotopy.mk γ))

/-- The discrete label's underlying value is exactly the original homotopical K₀ class. -/
theorem loopKZeroLabel_value (γ : Path E.kBasepoint E.kBasepoint) :
    (E.loopKZeroLabel γ).ofTopology =
      E.loopComponentsKZeroEquiv (ZerothHomotopy.mk γ) := rfl

/-- Equality of the actual labels is exactly joinedness of the original loops. -/
theorem loopKZeroLabel_eq_iff (γ δ : Path E.kBasepoint E.kBasepoint) :
    E.loopKZeroLabel γ = E.loopKZeroLabel δ ↔ Joined γ δ := by
  constructor
  · intro h
    have he := E.loopComponentsKZeroEquiv.injective (congrArg WithTopology.ofTopology h)
    exact Quotient.exact he
  · intro h
    exact congrArg (fun a ↦ WithTopology.toTopology ⊥ (E.loopComponentsKZeroEquiv a))
      (_root_.Quotient.sound h)

/-- Every original K₀ class is realized by an actual original based loop. -/
theorem loopKZeroLabel_surjective : Function.Surjective E.loopKZeroLabel := by
  intro a
  obtain ⟨γ, hγ⟩ := ZerothHomotopy.mk_surjective
    (E.loopComponentsKZeroEquiv.symm a.ofTopology)
  refine ⟨γ, ?_⟩
  apply WithTopology.ext
  change E.loopComponentsKZeroEquiv (ZerothHomotopy.mk γ) = a.ofTopology
  rw [hγ, Equiv.apply_symm_apply]

/-- The discrete neutral label retains the original multiplicative K₀ identity. -/
def discreteKZeroIdentity : E.DiscreteKZero := WithTopology.toTopology ⊥ 1

/-- The original constant loop has precisely the original neutral label. -/
theorem loopKZeroLabel_refl : E.loopKZeroLabel (Path.refl E.kBasepoint) =
    E.discreteKZeroIdentity := by
  apply WithTopology.ext
  change E.loopComponentsKZeroEquiv (ZerothHomotopy.mk (Path.refl E.kBasepoint)) = 1
  rw [loopComponentsKZeroEquiv_mk]
  change E.kZeroFundamentalGroupEquiv.symm 1 = 1
  exact map_one _

/-- Every original Q-loop component is genuinely open in its compact-open topology. -/
theorem isOpen_qLoop_pathComponent (γ : Path E.kBasepoint E.kBasepoint) :
    IsOpen (pathComponent γ) :=
  RankedChainOrder.isOpen_loop_pathComponent E.QCategory E.qZero γ

/-- Continuity of the original discrete K₀ classifier follows from the proved open components. -/
@[fun_prop]
theorem continuous_loopKZeroLabel : Continuous E.loopKZeroLabel := by
  apply continuous_discrete_rng.mpr
  intro a
  obtain ⟨γ, hγ⟩ := E.loopKZeroLabel_surjective a
  have he : E.loopKZeroLabel ⁻¹' {a} = pathComponent γ := by
    ext δ
    change E.loopKZeroLabel δ = a ↔ Joined γ δ
    rw [← hγ, E.loopKZeroLabel_eq_iff]
    exact ⟨Joined.symm, Joined.symm⟩
  rw [he]
  exact E.isOpen_qLoop_pathComponent γ

/-- The actual compact-open Q-loop space has this continuous discrete original K₀ classifier. -/
def continuousLoopKZeroLabel : C(Path E.kBasepoint E.kBasepoint, E.DiscreteKZero) :=
  ⟨E.loopKZeroLabel, E.continuous_loopKZeroLabel⟩

end CategoryTheory.ExactCategory.ExactStructure
