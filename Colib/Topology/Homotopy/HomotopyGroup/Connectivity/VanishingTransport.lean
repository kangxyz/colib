/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ComponentTranslation

/-!
# Finite vanishing through original maps and loop components

Finite connectivity gives surjectivity through its endpoint degree, and actual target paths
transfer vanishing to every point. The unchanged compact-open loop space loses exactly one
homotopy degree; its original component translation covers arbitrary displayed loops.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/Connectivity/VanishingTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original finite-degree vanishing, endpoint-degree surjectivity, actual
path transport and arbitrary displayed loop components are retained. -/
@[expose] public section
noncomputable section
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Singleton zeroth homotopy at one original point gives actual paths between every two points.
-/
theorem pathConnectedSpace_of_subsingleton_pi_zero (x : X)
    (h : Subsingleton (HomotopyGroup.Pi 0 X x)) : PathConnectedSpace X := by
  let := h
  let : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm.injective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk x⟩, inferInstance⟩

/-- Connectivity transfers source vanishing through the endpoint degree at every target point.
-/
theorem IsHomotopyConnectedMap.subsingleton_target {f : C(X, Y)} {n : ℕ}
    (hf : IsHomotopyConnectedMap f n) (k : ℕ) (hk : k ≤ n)
    (hX : ∀ x, Subsingleton (HomotopyGroup.Pi k X x)) (y : Y) :
    Subsingleton (HomotopyGroup.Pi k Y y) := by
  obtain ⟨x, hx⟩ := hf.component_surjective y
  let := hX x
  let : Subsingleton (HomotopyGroup.Pi k Y (f x)) :=
    (hf.homotopyGroupMap_surjective x k hk).subsingleton
  exact (pathTransport hx.somePath k).symm.injective.subsingleton

/-- Loop degree shift and actual component translation retain every original loop basepoint. -/
theorem subsingleton_pi_loop_of_succ (x : X) (k : ℕ)
    (h : Subsingleton (HomotopyGroup.Pi (k + 1) X x)) (γ : Path x x) :
    Subsingleton (HomotopyGroup.Pi k (Path x x) γ) := by
  let := h
  let : Subsingleton (HomotopyGroup.Pi k (Path x x) (Path.refl x)) :=
    (loopShiftEquiv (x := x) k).symm.injective.subsingleton
  exact (loopComponentHomotopyEquiv γ k).symm.injective.subsingleton

end Topology
