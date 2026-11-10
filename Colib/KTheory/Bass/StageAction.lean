/-
Copyright (c) 2026 OpenAI and Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.NaturalTrack

/-!
# Whole actions on finite Bass stages

The original Bass functor has equal left- and right-associated finite iterates.
Transporting only this equality defines the actual stage actions recursively.
These are the unchanged declarations from the finite normalization construction,
separated from its topology and stable-equivalence consequences.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.NormalizedStageMap
variable {C : Type u} [Category.{v} C]
/-- The two associations of the original finite Bass iterate are equal as entire functors. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:43"
  "adaptation" "Original finite Bass-stage recursion; same hypotheses and whole-cell comparison."]
theorem bass_succ_eq (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramIterate Q (i + 1)).obj F =
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) := by
  induction i generalizing F with
  | zero => rfl
  | succ i ih => exact ih ((strictDiagramFunctor Q).obj F)

end KTheory.Bass.NormalizedStageMap

namespace KTheory.Bass.NaturalTrack
open NormalizedStageMap
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
  {F : C ⥤ LoopPrespectrum.{w}}
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The action on the original right-associated Bass stages, with the named source transport. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageAction.lean:62"
  "adaptation" "Original finite Bass-stage recursion; same hypotheses and whole-cell comparison."]
def Track.stages (A : Track L c F) :
    ∀ i, Track L c ((strictDiagramIterate Q i).obj F)
  | 0 => A
  | i + 1 => ((A.stages i).bass Q χ hχ).cast (bass_succ_eq Q i F).symm

end KTheory.Bass.NaturalTrack
