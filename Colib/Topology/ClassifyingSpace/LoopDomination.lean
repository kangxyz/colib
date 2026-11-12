/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.LoopDomination
public import Colib.Topology.ClassifyingSpace.OpenLoopComponents

/-!
# Constructed realization domination of the original categorical based loops

Transport the actual metric-order domination through the previously proved
compact-open loop homotopy equivalence. Its right-inverse homotopy supplies
the final endpoint, so the composite on the original loop space is actually
homotopic to its identity. Object and morphism universes remain independent.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/ClassifyingSpace/LoopDomination.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology Simplicial
universe u v
namespace CategoryTheory.RankedChainOrder

variable (C : Type u) [Category.{v} C] (c : C)

/-- Actual categorical-loop domination, transported with the genuine inverse homotopy. -/
def universalLoopDominationData :
    Σ K : SSet.{max u v},
      Σ a : C(Path (classifyingSpacePoint c) (classifyingSpacePoint c), |K|),
        Σ b : C(|K|, Path (classifyingSpacePoint c) (classifyingSpacePoint c)),
          (b.comp a).Homotopy (ContinuousMap.id _) := by
  let e := universalMetricLoopHomotopyEquiv C c
  let D := MetricOrderComplex.loopDominationData (universalResolutionVertex C c)
  let a := D.2.1.comp e.invFun
  let b := e.toFun.comp D.2.2.1
  have H : (b.comp a).Homotopy (e.toFun.comp e.invFun) := by
    simpa only [a, b, ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      (ContinuousMap.Homotopy.refl e.toFun).comp (D.2.2.2.compContinuousMap e.invFun)
  exact ⟨D.1, a, b, H.trans e.right_inv.some⟩

end CategoryTheory.RankedChainOrder
