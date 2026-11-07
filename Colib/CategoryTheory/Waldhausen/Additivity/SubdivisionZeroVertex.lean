/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridBasedHomotopy
public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalBisimplicial

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, hypotheses, universes,
whole faces and chosen-zero surfaces are preserved. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The original constant-zero grid in degrees (delta[0], [0]). -/
def subdivisionZeroVertex :
    (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ :=
  zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌)

/-- The original first-half endpoint takes the stated zero grid to the original zero grid. -/
@[simp]
theorem horizontalEndpoint_zeroVertex :
    (SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))).app
      (op ⦋0⦌) (subdivisionZeroVertex V) = diagonalZeroVertex V := rfl


end CategoryTheory.Waldhausen.Additivity
