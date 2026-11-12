/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowLooping

/-!
# Whole row squares under the original finite Bass homotopy construction

An original coefficient-natural homotopy with an actual whole row square descends through the
same three span cells, the same two cone cells, and the same parameter-looping construction.
The statement applies equally to the specified source null: endpoints alone never replace its
whole-time square. The comparison is the actual strict-diagram comparison used in `ConeTrack`.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowInterchange
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (pF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (nF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (pG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (nG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  {η θ : F ⟶ G} (H : ∀ X, Homotopy (η.app X) (θ.app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
    (G.map g).map n ((H X).level n (r, x)) =
      (H Y).level n (r, (F.map g).map n x))
  (hrow : ∀ X k r x, qG X k ((H X).level (k + 3) (r, x)) =
    (H X).level (k + 3) (r, qF X k x))

include hrow

/-- The prescribed whole overlap homotopy preserves the genuine row square on all three cells. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowHomotopy.lean:44"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem span_homotopy (X : C) (k : ℕ) (r : unitInterval)
    (x : (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3)) :
    span Q G qG pG nG X k
      ((diagramSquareMapHomotopy H hH (Q.obj X)).span.level (k + 3) (r, x)) =
      (diagramSquareMapHomotopy H hH (Q.obj X)).span.level (k + 3)
        (r, span Q F qF pF nF X k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y =>
        exact congrArg (HomotopyPushout.left (G.map (Q.obj X).left.hom)
          (G.map (Q.obj X).hom.left) (k + 3)) (hrow (Q.obj X).left.right k r y)
      | inr y =>
        exact congrArg (HomotopyPushout.right (G.map (Q.obj X).left.hom)
          (G.map (Q.obj X).hom.left) (k + 3)) (hrow (Q.obj X).right.left k r y)
    | inr z =>
      exact congrArg (fun y => HomotopyPushout.cylinder (G.map (Q.obj X).left.hom)
        (G.map (Q.obj X).hom.left) (k + 3) (z.1, y)) (hrow (Q.obj X).left.left k r z.2)

/-- The original moving cone preserves the whole row square without changing either height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowHomotopy.lean:64"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem cone_homotopy (X : C) (k : ℕ) (r : unitInterval)
    (x : ((ConeTrack.diagram Q F).obj X).space (k + 3)) :
    cone Q G qG pG nG X k
      ((diagramSquareMapHomotopy H hH (Q.obj X)).cone.level (k + 3) (r, x)) =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level (k + 3)
        (r, cone Q F qF pF nF X k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y =>
      exact congrArg ((mappingConeInclusion
        (StrictSquare.comparison (G.mapArrow.mapArrow.obj (Q.obj X)))).map (k + 3))
          (hrow (Q.obj X).right.right k r y)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy
        (StrictSquare.comparison (G.mapArrow.mapArrow.obj (Q.obj X)))).level (k + 3) (z.1, y))
          (span_homotopy Q qF pF nF qG pG nG H hH hrow X k r z.2)

/-- Parameter looping keeps the old loop, whole homotopy and all quotient heights independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowHomotopy.lean:82"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem bass_homotopy (X : C) (k : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space (k + 3)) :
    bass Q G qG pG nG X k ((strictDiagramMapHomotopy H hH Q X).level (k + 3) (r, x)) =
      (strictDiagramMapHomotopy H hH Q X).level (k + 3) (r, bass Q F qF pF nF X k x) :=
  RowInterchange.parameterLoop_homotopy _ _ _ _
    (diagramSquareMapHomotopy H hH (Q.obj X)).cone
      (cone_homotopy Q qF pF nF qG pG nG H hH hrow X) k r x

end KTheory.Bass.DiagramRowInterchange
