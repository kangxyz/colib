/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.LoopEquiconnection
public import Colib.Topology.Realization.MetricRealizationDomination

/-!
# Actual realization domination of literal metric-order based loops

This instantiates the constructive generic metric/numerable theorem with the
proved G4 connector and actual convex-open cover. No loop model equivalence,
domination, or inverse is supplied as a hypothesis. The chosen maps below
are selected only after their simultaneous existence is proved.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/LoopDomination.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology Simplicial
universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P] (p : P)

/-- The constructed generic domination applies to the unchanged compact-open metric loop space. -/
theorem exists_loop_realization_domination :
    ∃ (K : SSet.{u}) (a : C(Path (vertex p) (vertex p), |K|))
      (b : C(|K|, Path (vertex p) (vertex p))),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id _)) :=
  NumerableConnectorCover.exists_metric_realization_domination (loopEquiconnection p)
    (fun W : LoopConvexOpenSets p ↦ W.val) (fun W ↦ W.property.1)
    (fun W ↦ W.property.2) (loopConvexOpenSets_covers p)

/-- Chosen actual maps and their actual homotopy, obtained from the proved construction. -/
def loopDominationData :
    Σ K : SSet.{u}, Σ a : C(Path (vertex p) (vertex p), |K|),
      Σ b : C(|K|, Path (vertex p) (vertex p)),
        (b.comp a).Homotopy (ContinuousMap.id _) :=
  Classical.choice (by
    obtain ⟨K, a, b, ⟨H⟩⟩ := exists_loop_realization_domination p
    exact ⟨⟨K, a, b, H⟩⟩)

end Topology.MetricOrderComplex
