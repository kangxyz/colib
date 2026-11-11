/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowCellIteration


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

variable (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (A : NaturalTrack.Track L c F)
  (D : Family L c F q hp hn hs A)
variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))


example : iterateFamily L c Q χ hχ 0 F q hp hn hs A D = D := rfl

example (i : ℕ) :
    Family L c ((strictDiagramIterate Q i).obj F)
      (DiagramRowInterchange.iterate Q i F q hp hn)
      (DiagramRowInterchange.iterate_point Q i F q hp hn)
      (DiagramRowInterchange.iterate_naturality Q i F q hp hn)
      (DiagramRowInterchange.iterate_structure Q i F q hp hn hs)
      (A.stages Q χ hχ i) := iterateFamily L c Q χ hχ i F q hp hn hs A D

example (i : ℕ) {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space n) :
    ((DiagramRowRefinement.diagram ((strictDiagramIterate Q i).obj F)
      (DiagramRowInterchange.iterate Q i F q hp hn)
      (DiagramRowInterchange.iterate_point Q i F q hp hn)
      (DiagramRowInterchange.iterate_naturality Q i F q hp hn)).map (L.map g)).map n
      (((iterateFamily L c Q χ hχ i F q hp hn hs A D).val X).level n (t, x)) =
    ((iterateFamily L c Q χ hχ i F q hp hn hs A D).val Y).level n
      (t, (((strictDiagramIterate Q i).obj F).map g).map n x) :=
  (iterateFamily L c Q χ hχ i F q hp hn hs A D).property.1 g n t x

example (i : ℕ) (X : C) (t : unitInterval) :
    ((iterateFamily L c Q χ hχ i F q hp hn hs A D).val X).at t =
      ((A.stages Q χ hχ i).homotopy X).at t ≫
        (DiagramRowRefinement.comparison ((strictDiagramIterate Q i).obj F)
          (DiagramRowInterchange.iterate Q i F q hp hn)
          (DiagramRowInterchange.iterate_point Q i F q hp hn)
          (DiagramRowInterchange.iterate_naturality Q i F q hp hn)
          (DiagramRowInterchange.iterate_structure Q i F q hp hn hs)).app (L.obj X) :=
  (iterateFamily L c Q χ hχ i F q hp hn hs A D).property.2 X t

example (i : ℕ) :
    (A.bass Q χ hχ).stages Q χ hχ i = A.stages Q χ hχ (i + 1) :=
  NaturalTrack.Track.stages_bass Q χ hχ A i

example (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).obj F =
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) :=
  NormalizedStageMap.bass_succ_eq Q i F

end KTheory.Bass.DiagramRowCell
