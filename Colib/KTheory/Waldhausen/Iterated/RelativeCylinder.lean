/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Double
public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.RelativeTime
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.OrdinaryRows
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.CoarseEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# The literal first S-cylinder in the actual relative K-theory total

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/RelativeCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, lines 67–144.
This uses the actual all-weak relative total, not the separate stage path diagram.
Its tail is the original suspension cylinder at every simplex and time, and both
original endpoint maps and the entire homotopy are retained.

The five ordinal time declarations are reused from their lower native owner.
The lifted row belongs to this relative-total K-theory application and reuses
the existing all-weak structure, its actual relative category and its witnesses.
The ordinal time API remains at its existing categorical owner.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open Fibration Fibration.RelativeRows
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The actual one-row time construction, with honest all-weak acyclicity witnesses. -/
def relativeTimeRow {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : C ⥤ RelativeRows.Obj (AllWeak.nested
    W) n :=
  (RelativeRows.objects (AllWeak.nested W) n).lift (suspensionRow W (relativeTime τ))
    (fun _ _ ↦ AllWeak.acyclic W _)

lemma relativeTimeRow_exact {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    IsExact W.cof W.weq (RelativeRows.waldhausenStructure (AllWeak.nested W) n).cof
      (RelativeRows.waldhausenStructure (AllWeak.nested W) n).weq (relativeTimeRow W τ) where
  zero h := IsZero.of_full_of_faithful_of_isZero (RelativeRows.forget (AllWeak.nested W) n) _
    ((suspensionRow_exact W (relativeTime τ)).zero h)
  cofibration f hf := (suspensionRow_exact W (relativeTime τ)).cofibration f hf
  weak f hf := (suspensionRow_exact W (relativeTime τ)).weak f hf
  pushout hf h := IsPushout.of_map_of_faithful (RelativeRows.forget (AllWeak.nested W) n)
    ((suspensionRow_exact W (relativeTime τ)).pushout hf h)

lemma relativeTimeRow_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    relativeTimeRow W τ ⋙ RelativeRows.reindex (AllWeak.nested W) α =
      relativeTimeRow W (α ≫ τ) := by
  apply RelativeRows.functor_eq_of_comp_forget (AllWeak.nested W)
  change suspensionRow W (relativeTime τ) ⋙ QuotientRows.reindex W (addInitial.map α) =
    suspensionRow W (relativeTime (α ≫ τ))
  rw [← suspensionRow_reindex, relativeTime_reindex]

lemma relativeTimeRow_zero (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 0) =
      (Functor.const C).obj (RelativeRows.zero (AllWeak.nested W) n) := by
  apply RelativeRows.functor_eq_of_comp_forget (AllWeak.nested W)
  change suspensionRow W (relativeTime (n.const ⦋1⦌ 0)) = _
  rw [relativeTime_zero, suspensionRow_const]
  rfl

lemma relativeTimeRow_one (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 1) = fiber (AllWeak.nested W) n := rfl

/-- The original suspension cylinder lifts to the actual contractible relative total. -/
def relativeCylinder : sSet W.cof W.weq ⊗ Δ[1] ⟶
    SSet.diagonalSSet (relativeSRows (AllWeak.nested W)) where
  app n := ↾fun z ↦ ⟨z.1.val ⋙ relativeTimeRow W z.2.down,
    z.1.property.postcomp (relativeTimeRow_exact W z.2.down)⟩
  naturality n m α := by
    ext z : 3
    apply Subtype.ext
    change (gridMap α.unop ⋙ z.1.val) ⋙ relativeTimeRow W (α.unop ≫ z.2.down) =
      (gridMap α.unop ⋙ z.1.val) ⋙ relativeTimeRow W z.2.down ⋙ RelativeRows.reindex
        (AllWeak.nested W) α.unop
    rw [relativeTimeRow_reindex]

/-- The original acyclic-tail projection followed by the original witness-forgetting iso. -/
def relativeTail : SSet.diagonalSSet (relativeSRows (AllWeak.nested W)) ⟶ doubleDiagonal W :=
  SSet.diagonalMap (tailSRows (AllWeak.nested W)) ≫ (AllWeak.ordinaryDiagonalIso W).hom

lemma relativeCylinder_tail : relativeCylinder W ≫ relativeTail W = suspensionCylinder W := by
  ext n z : 4
  apply Subtype.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

lemma relativeCylinder_zero : SSet.ι₀ ≫ relativeCylinder W =
    SSet.const (totalZeroVertex (AllWeak.nested W)) := by
  ext n z : 4
  apply Subtype.ext
  change z.val ⋙ relativeTimeRow W (n.unop.const ⦋1⦌ 0) = _
  rw [relativeTimeRow_zero]
  rfl

lemma relativeCylinder_one : SSet.ι₁ ≫ relativeCylinder W = totalFiberInclusion (AllWeak.nested
    W) := by
  ext n z : 4
  apply Subtype.ext
  rfl

/-- The lifted original cylinder joins the literal zero to the original split-fiber map. -/
def relativeHomotopy : SSet.Homotopy (SSet.const (X := sSet W.cof W.weq)
    (totalZeroVertex (AllWeak.nested W))) (totalFiberInclusion (AllWeak.nested W)) where
  h := relativeCylinder W
  h₀ := relativeCylinder_zero W
  h₁ := relativeCylinder_one W
  rel := by ext n z; exact z.1.property.elim

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_ref "Waldhausen1985" "Section 1.5, Lemmas 1.5.1-1.5.2, pp. 341-342"
  "adaptation" "The literal first S-cylinder and its complete relative-total lift"]
  CategoryTheory.Waldhausen.IteratedS.relativeHomotopy
