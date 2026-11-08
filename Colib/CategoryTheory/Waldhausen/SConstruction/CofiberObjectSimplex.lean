/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoFaces
public import Colib.CategoryTheory.Waldhausen.SConstruction.ObjectSimplex

/-! # The actual displayed cofiber simplex and its three object faces

These are unchanged native moves from `GrothendieckComparison/CofiberObjectTrack`
at frozen Colib commit `7e0574e15afed4570c71bb573119ec48574097f1`, lines 38–52.
The original source is `Quillen/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean`
lines 30–44 at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Both declarations retain the actual row, its chosen zero and every simplicial face.
No realization or K-theory is imported. Native compilation remains pending.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
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

end CategoryTheory.Waldhausen.Structure
