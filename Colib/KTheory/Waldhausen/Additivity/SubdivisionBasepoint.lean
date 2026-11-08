/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.SubdivisionZeroVertex
public import Colib.KTheory.Waldhausen.WeakGridBasedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.RealizationHomotopy
public import Colib.Topology.Realization.EdgePath

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, hypotheses, universes,
whole faces and chosen-zero surfaces are preserved. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet SSet.MixedOrdinalCylinder
open scoped Simplicial Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- Its actual realization point, with no choice of path. -/
def subdivisionBasepoint :
    |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)| :=
  SSet.realizationPoint (subdivisionZeroVertex V)

/-- The prescribed actual endpoint map preserves the displayed realization points. -/
@[simp]
theorem horizontalEndpoint_basepoint :
    realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))
      (subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex V) := by
  rw [subdivisionBasepoint]
  exact SSet.realizationPoint_naturality _ _


end CategoryTheory.Waldhausen.Additivity
