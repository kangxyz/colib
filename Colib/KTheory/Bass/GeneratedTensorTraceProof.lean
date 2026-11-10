/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.GeneratedTensorTrace

/-! Left-generated finite tensor recipes, defined without invoking iterateFamily. -/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.TensorGeneratedRecipe
open DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Uniform induction constructs every trace from the independent generator step,
including the transformed starting diagram at every successor. -/
@[colib_tag "COL-0528", colib_ref "quillen"
  "Quillen/KTheory/Bass/GeneratedTensorTraceProof.lean:27"
  "adaptation" "Original generator-defined Bass step and finite trace induction."]
theorem iterateFamily_generated (i : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (A : NaturalTrack.Track L c F) (D : Family L c F q hp hn hs A) :
    GeneratedTrace L c Q χ hχ i F q hp hn hs A D
      (iterateFamily L c Q χ hχ i F q hp hn hs A D).val := by
  induction i generalizing F with
  | zero => exact HEq.rfl
  | succ i ih =>
    let next : Family L c ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn)
        (DiagramRowInterchange.bass_structure Q F q hp hn hs)
        (A.bass Q χ hχ) :=
      ⟨step L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ,
        step_naturality L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ,
        step_at_eq L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ⟩
    refine ⟨next, step_generated L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ, ?_⟩
    exact ih ((strictDiagramFunctor Q).obj F)
      (DiagramRowInterchange.bass Q F q hp hn)
      (DiagramRowInterchange.bass_point Q F q hp hn)
      (DiagramRowInterchange.bass_naturality Q F q hp hn)
      (DiagramRowInterchange.bass_structure Q F q hp hn hs)
      (A.bass Q χ hχ) next

end KTheory.Bass.TensorGeneratedRecipe
