/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoFaces
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops
public import Colib.Topology.Realization.TriangleHomotopy

/-!
# The displayed cofiber triangle and its specified object-loop homotopy

The literal two-row supplies the full simplex, constant in the nerve coordinate.
Its faces are quotient, middle and source, so its relative homotopy composes source
followed by quotient to middle. Comparison time and loop time remain independent.

Implementation provenance: the complete mathematical content of
`Quillen/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean` (64 lines)
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual characteristic map and
data-valued triangle homotopy are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- Repeat the genuine displayed quotient row in the original nerve coordinate. -/
def cofiberObjectSimplex : (sSet W.cof W.weq) _⦋2⦌ :=
  W.rowSimplex (QuotientRows.cofiberTwoRow W i q hi hQ)

/-- The three actual diagonal faces are the original quotient, middle and source object edges. -/
theorem cofiberObjectSimplex_face (k : Fin 3) :
    (sSet W.cof W.weq).δ k (W.cofiberObjectSimplex i q hi hQ) =
      W.kZeroObjectSimplex (QuotientRows.cofiberFaceObject (A := A) (B := B) (Q := Q) k) := by
  apply Subtype.ext
  change intervalProjection ⦋1⦌ ⋙
      (QuotientRows.indexMap (SimplexCategory.δ k) ⋙
        QuotientRows.cofiberTwoDiagram W i q (QuotientRows.cofiberTwo_comp_eq_zero W i q hQ)) =
    intervalProjection ⦋1⦌ ⋙ CategoryTheory.Waldhausen.QuotientRows.oneDiagram W
      (QuotientRows.cofiberFaceObject (A := A) (B := B) (Q := Q) k)
  rw [QuotientRows.cofiberTwoDiagram_face]

/-- The actual original cofiber simplex composes source followed by quotient to middle. -/
def cofiberObjectCompStruct : SSet.Edge.CompStruct
    (W.kZeroObjectEdge A) (W.kZeroObjectEdge Q) (W.kZeroObjectEdge B) where
  simplex := W.cofiberObjectSimplex i q hi hQ
  d₂ := W.cofiberObjectSimplex_face i q hi hQ 2
  d₀ := W.cofiberObjectSimplex_face i q hi hQ 0
  d₁ := W.cofiberObjectSimplex_face i q hi hQ 1

/-- The specified full-triangle homotopy of the original canonical object loops. -/
def cofiberObjectLoopTrack :
    ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop Q)).Homotopy (W.kZeroObjectLoop B) :=
  realizationEdgeCompositionHomotopy (W.cofiberObjectCompStruct i q hi hQ)

/-- Both parameters are exactly those of the explicit original triangle homotopy. -/
theorem cofiberObjectLoopTrack_apply (r t : unitInterval) :
    W.cofiberObjectLoopTrack i q hi hQ (r, t) =
      realizationEdgeCompositionHomotopy (W.cofiberObjectCompStruct i q hi hQ) (r, t) := rfl

end CategoryTheory.Waldhausen.Structure
