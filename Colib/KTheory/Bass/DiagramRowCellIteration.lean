/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowCellStep
public import Colib.KTheory.Bass.DiagramRowIteration
public import Colib.KTheory.Bass.TrackBassIteration

/-! # Constructive iteration of the independent whole row cell

Each successor applies the actual moving-square cone, index transport, forward row strength
and explicit loop/row conversion. The subtype merely retains the proved naturality and whole
comparison of this explicit cell; it makes no choice of fillers or new compatibility assumption.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L)

/-- An explicit whole cell together with the two properties already proved for that cell. -/
@[colib_tag "COL-0527", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellIteration.lean:30"
  "adaptation" "Original finite Bass-stage recursion; same hypotheses and whole-cell comparison."]
def Family (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (A : NaturalTrack.Track L c F) :=
  { H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
      ((input L c F q hp hn hs).app X) //
    (∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
      ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
        ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x)) ∧
    (∀ X t, (H X).at t = (A.homotopy X).at t ≫
      (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X)) }

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The finite cells follow the same recursion on the initial diagram as the computed row maps. -/
@[colib_tag "COL-0527", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellIteration.lean:53"
  "adaptation" "Original finite Bass-stage recursion; same hypotheses and whole-cell comparison."]
def iterateFamily (i : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (A : NaturalTrack.Track L c F) (D : Family L c F q hp hn hs A) :
    Family L c ((strictDiagramIterate Q i).obj F)
      (DiagramRowInterchange.iterate Q i F q hp hn)
      (DiagramRowInterchange.iterate_point Q i F q hp hn)
      (DiagramRowInterchange.iterate_naturality Q i F q hp hn)
      (DiagramRowInterchange.iterate_structure Q i F q hp hn hs)
      (A.stages Q χ hχ i) :=
  match i with
  | 0 => D
  | i + 1 =>
    let next : Family L c ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn)
        (DiagramRowInterchange.bass_structure Q F q hp hn hs)
        (A.bass Q χ hχ) :=
      ⟨step L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ,
        step_naturality L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ,
        step_at_eq L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ⟩
    let result := iterateFamily i ((strictDiagramFunctor Q).obj F)
      (DiagramRowInterchange.bass Q F q hp hn)
      (DiagramRowInterchange.bass_point Q F q hp hn)
      (DiagramRowInterchange.bass_naturality Q F q hp hn)
      (DiagramRowInterchange.bass_structure Q F q hp hn hs) (A.bass Q χ hχ) next
    ⟨result.val, result.property.1, fun X t =>
      (result.property.2 X t).trans
        (congrArg (fun B : NaturalTrack.Track L c ((strictDiagramIterate Q (i + 1)).obj F) =>
          (B.homotopy X).at t ≫
            (DiagramRowRefinement.comparison ((strictDiagramIterate Q (i + 1)).obj F)
              (DiagramRowInterchange.iterate Q (i + 1) F q hp hn)
              (DiagramRowInterchange.iterate_point Q (i + 1) F q hp hn)
              (DiagramRowInterchange.iterate_naturality Q (i + 1) F q hp hn)
              (DiagramRowInterchange.iterate_structure Q (i + 1) F q hp hn hs)).app (L.obj X))
          (NaturalTrack.Track.stages_bass Q χ hχ A i))⟩

end KTheory.Bass.DiagramRowCell
