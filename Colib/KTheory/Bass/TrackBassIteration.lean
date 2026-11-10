/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StageAction

/-! # The original Bass action under recursion on the initial diagram

The fixed original finite action agrees with applying one Bass action first and continuing
on that actual diagram. Only the original functor-association equality proofs are transported.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.NaturalTrack
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
  {F : C ⥤ LoopPrespectrum.{w}}
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Recursing on the initial Bass diagram retains the original whole stage track. -/
@[colib_tag "COL-0527", colib_ref "quillen"
  "Quillen/KTheory/Bass/TrackBassIteration.lean:28"
  "adaptation" "Original finite Bass-stage recursion; same hypotheses and whole-cell comparison."]
theorem Track.stages_bass (A : Track L c F) (i : ℕ) :
    (A.bass Q χ hχ).stages Q χ hχ i = A.stages Q χ hχ (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Track.stages]
    rw [ih]
    rfl

end KTheory.Bass.NaturalTrack
