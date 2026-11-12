/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroPointClass

/-! # Fundamental groups and loop-space components

The original loop-degree shift from `Quillen/Topology/ClassifyingSpace/FundamentalGroup.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual path representatives.
-/
@[expose] public noncomputable section
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] (x : X)
/-- The original loop-degree shift, expressed using the native fundamental group. -/
def fundamentalGroupLoopComponentEquiv :
    FundamentalGroup X x ≃ HomotopyGroup.Pi 0 (Path x x) (Path.refl x) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.symm.trans (loopShiftEquiv 0)

lemma fundamentalGroupLoopComponentEquiv_path (γ : Path x x) :
    fundamentalGroupLoopComponentEquiv x (FundamentalGroup.fromPath ⟦γ⟧) =
      zeroPointClass (Path.refl x) γ := by
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  rfl
end Topology
