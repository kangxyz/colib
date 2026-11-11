/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-! # Original coefficient-natural null/unit/null seed word

Only the original whole-word construction and its same-time naturality are selected.
No comparison under Bass, stability or telescope statement is assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.HomotopyWord
variable {C : Type u} [Category.{v} C]
variable {F G : C ⥤ LoopPrespectrum.{w}} {a b c : F ⟶ G}

/-- Same-time naturality of the supplied actual family. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/HomotopyWord.lean:28"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
abbrev Natural (H : ∀ X, Homotopy (a.app X) (b.app X)) : Prop :=
  ∀ {X Y} (f : X ⟶ Y) n r x,
    (G.map f).map n ((H X).level n (r, x)) =
      (H Y).level n (r, (F.map f).map n x)

/-- Reversal keeps the original naturality equation at reversed time. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/HomotopyWord.lean:34"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem natural_symm (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) :
    Natural (fun X => (H X).symm) := fun f n r x => hH f n (unitInterval.symm r) x

/-- The original half-clock concatenation preserves same-time naturality. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/HomotopyWord.lean:38"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem natural_trans (H : ∀ X, Homotopy (a.app X) (b.app X))
    (K : ∀ X, Homotopy (b.app X) (c.app X)) (hH : Natural H) (hK : Natural K) :
    Natural (fun X => (H X).trans (K X)) := by
  intro X Y f n r x
  change (G.map f).map n (((H X).levelHomotopy n).trans ((K X).levelHomotopy n) (r,x)) =
    ((H Y).levelHomotopy n).trans ((K Y).levelHomotopy n) (r, (F.map f).map n x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH f n _ x
  · exact hK f n _ x

/-- Original postcomposition preserves the naturality of the whole family. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/HomotopyWord.lean:50"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem natural_postcomp {D : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) (j : G ⟶ D) :
    Natural (a := a ≫ j) (b := b ≫ j) (fun X => (H X).postcomp (j.app X)) := by
  intro X Y f n r x
  change ((j.app X) ≫ D.map f).map n ((H X).level n (r,x)) =
    (j.app Y).map n ((H Y).level n (r, (F.map f).map n x))
  rw [← j.naturality]
  exact congrArg ((j.app Y).map n) (hH f n r x)

end KTheory.Bass.HomotopyWord
