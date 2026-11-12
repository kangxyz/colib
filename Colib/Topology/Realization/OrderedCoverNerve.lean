/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The actual ordered simplicial nerve of a cover

Simplices are monotone vertex lists whose cover members have a common point.
Repeated vertices are allowed and restriction by every simplex operator
preserves the witness. No realization maps are postulated here.
-/

open SSet CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/OrderedCoverNerve.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u v
namespace Topology.NumerableConnectorCover
variable {A : Type u} {ι : Type v} [LinearOrder ι]

/-- The ordered cover nerve as an actual simplicial subcomplex of the order nerve. -/
def orderedNerve (W : ι → Set A) : (nerve ι).Subcomplex where
  obj n := {s | ∃ x, ∀ j, x ∈ W (s.obj j)}
  map f := by
    rintro s ⟨x, hx⟩
    exact ⟨x, fun j ↦ hx (f.unop.toOrderHom j)⟩

/-- The original intersection witness also works after every simplex restriction. -/
theorem orderedNerve_commonPoint (W : ι → Set A) {n : SimplexCategoryᵒᵖ}
    (s : (orderedNerve W).toSSet.obj n) :
    ∃ x, ∀ j, x ∈ W (s.1.obj j) := s.2

end Topology.NumerableConnectorCover
