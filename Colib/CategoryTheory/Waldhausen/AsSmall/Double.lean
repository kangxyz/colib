/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Functoriality
public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic

/-!
# Original small-model transport on both S-directions

Actual quotient-row postcomposition transports the double S-construction to the original small
model even when the original object and morphism universes differ. The genuine one-step row and
its suspension cylinder are preserved with the original chosen zero, without a universe-equality
assumption on the source category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Original small-model postcomposition on every actual quotient-row S-space. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SmallModel/Double.lean:31"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
def asSmallDoubleMap : doubleS W ⟶ doubleS W.asSmall where
  app n := {
    app m := ↾fun A => ⟨A.val ⋙
      QuotientRows.postcompose W W.asSmall W.asSmall_up_exact n.unop,
      A.property.postcomp
        (QuotientRows.postcompose_exact W W.asSmall W.asSmall_up_exact n.unop)⟩
    naturality m l α := by
      ext A : 3
      apply Subtype.ext
      apply CategoryTheory.Functor.ext (fun _ => rfl) }
  naturality n m α := by
    ext k A : 4
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The diagonal map retains both original row directions. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SmallModel/Double.lean:47"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
def asSmallDoubleDiagonalMap : doubleDiagonal W ⟶ doubleDiagonal W.asSmall :=
  SSet.diagonalMap (asSmallDoubleMap W)

/-- The original small-model functor takes the whole suspension row to the same original row. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SmallModel/Double.lean:51"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem asSmall_suspensionRow {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    suspensionRow W τ ⋙ QuotientRows.postcompose W W.asSmall W.asSmall_up_exact n =
      AsSmall.up ⋙ suspensionRow W.asSmall τ := by
  change (QuotientRows.oneEmbedding W ⋙ QuotientRows.reindex W τ) ⋙ _ = _
  rw [Functor.assoc, ← QuotientRows.postcompose_reindex W W.asSmall W.asSmall_up_exact τ,
    ← Functor.assoc,
    QuotientRows.oneEmbedding_postcompose W W.asSmall W.asSmall_up_exact rfl]
  rfl

/-- The entire first-row cylinder survives original small-model transport in both directions. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SmallModel/Double.lean:61"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem asSmall_suspensionCylinder :
    (W.asSmallSSetIso.hom ▷ Δ[1]) ≫ suspensionCylinder W.asSmall =
      suspensionCylinder W ≫ W.asSmallDoubleDiagonalMap := by
  ext n z : 4
  apply Subtype.ext
  change z.1.val ⋙ AsSmall.up ⋙ suspensionRow W.asSmall z.2.down =
    z.1.val ⋙ suspensionRow W z.2.down ⋙
      QuotientRows.postcompose W W.asSmall W.asSmall_up_exact n.unop
  rw [W.asSmall_suspensionRow]

end CategoryTheory.Waldhausen.Structure
