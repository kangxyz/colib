/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow

/-! # Actual object simplices of the Waldhausen S-construction

Implementation provenance: unchanged native definitions extracted from `ObjectLoops` in
`Colib/KTheory/Waldhausen/GrothendieckComparison/`, frozen parent `20c70502`.
The original implementation is `Quillen/Waldhausen/GrothendieckComparison/ObjectLoops.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
names, namespaces, declaration bodies, hypotheses and universe parameters are unchanged.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Forget the nerve coordinate of a diagonal grid. -/
def intervalProjection (n : SimplexCategory) : Grid n ⥤ Interval n :=
  (show Monotone (fun p : Grid n ↦ p.2) from fun _ _ h ↦ h.2).functor

/-- A genuine quotient row repeated identically in the nerve direction. -/
def rowSimplex {n : SimplexCategory} (F : QuotientRows.Obj W n) :
    (sSet W.cof W.weq).obj (op n) :=
  ⟨intervalProjection n ⋙ F.obj, {
    zero _ i := F.property.zero i
    cofibration _ i j k hij hjk := F.property.cofibration i j k hij hjk
    quotient _ i j k hij hjk := F.property.quotient i j k hij hjk
    weak s t i j hst hij := by
      change W.weq (F.obj.map (𝟙 (interval i j hij)))
      rw [F.obj.map_id]
      exact W.weq.id_mem (F.obj.obj (interval i j hij)) }⟩

/-- The genuine diagonal 1-simplex whose original quotient row is `(0,X,0)`. -/
def kZeroObjectSimplex (X : C) : (sSet W.cof W.weq) _⦋1⦌ :=
  rowSimplex W ((QuotientRows.oneEmbedding W).obj X)

end CategoryTheory.Waldhausen.Structure
