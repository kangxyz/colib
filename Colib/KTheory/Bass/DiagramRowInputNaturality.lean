/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowIteration

/-!
# Row interchange under transformations of the original diagram

Equivariance of an actual input transformation descends through the original
span, cone and parameter loop, then through every finite Bass iterate.
This is naturality in the input diagram, independent of coefficient naturality.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowInterchange
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hpF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hnF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (hpG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (hnG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))

include hη

/-- The input transformation preserves each original span cell and its overlap coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInputNaturality.lean:40"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem span_input_naturality (X : C) (k : ℕ)
    (x : (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3)) :
    span Q G qG hpG hnG X k
      ((StrictSquare.spanMap (diagramSquareMap η (Q.obj X))).map (k + 3) x) =
    (StrictSquare.spanMap (diagramSquareMap η (Q.obj X))).map (k + 3)
      (span Q F qF hpF hnF X k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y =>
        exact congrArg (HomotopyPushout.left (G.map (Q.obj X).left.hom)
          (G.map (Q.obj X).hom.left) (k + 3)) (hη (Q.obj X).left.right k y)
      | inr y =>
        exact congrArg (HomotopyPushout.right (G.map (Q.obj X).left.hom)
          (G.map (Q.obj X).hom.left) (k + 3)) (hη (Q.obj X).right.left k y)
    | inr z =>
      exact congrArg (fun y => HomotopyPushout.cylinder (G.map (Q.obj X).left.hom)
        (G.map (Q.obj X).hom.left) (k + 3) (z.1, y)) (hη (Q.obj X).left.left k z.2)

/-- The actual input transformation is equivariant on the entire original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInputNaturality.lean:60"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem cone_input_naturality (X : C) (k : ℕ)
    (x : ((ConeTrack.diagram Q F).obj X).space (k + 3)) :
    cone Q G qG hpG hnG X k (((ConeTrack.map Q η).app X).map (k + 3) x) =
      ((ConeTrack.map Q η).app X).map (k + 3) (cone Q F qF hpF hnF X k x) := by
  apply RowInterchange.cone_map
  · exact span_input_naturality Q qF hpF hnF qG hpG hnG η hη X
  · exact hη (Q.obj X).right.right

/-- Parameter looping preserves input naturality without exchanging its loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInputNaturality.lean:69"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem bass_input_naturality (X : C) (k : ℕ)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space (k + 3)) :
    bass Q G qG hpG hnG X k ((((strictDiagramFunctor Q).map η).app X).map (k + 3) x) =
      (((strictDiagramFunctor Q).map η).app X).map (k + 3)
        (bass Q F qF hpF hnF X k x) :=
  RowInterchange.parameterLoop_map _ _ _ _ ((ConeTrack.map Q η).app X)
    (cone_input_naturality Q qF hpF hnF qG hpG hnG η hη X) k x

/-- Every finite original Bass stage is natural in an equivariant input transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInputNaturality.lean:78"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem iterate_input_naturality (i : ℕ) (X : C) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) :
    iterate Q i G qG hpG hnG X k
        ((((strictDiagramIterate Q i).map η).app X).map (k + 3) x) =
      (((strictDiagramIterate Q i).map η).app X).map (k + 3)
        (iterate Q i F qF hpF hnF X k x) := by
  induction i generalizing F G with
  | zero => exact hη X k x
  | succ i ih =>
    exact ih (bass Q F qF hpF hnF) (bass_point Q F qF hpF hnF)
      (bass_naturality Q F qF hpF hnF) (bass Q G qG hpG hnG)
      (bass_point Q G qG hpG hnG) (bass_naturality Q G qG hpG hnG)
      ((strictDiagramFunctor Q).map η)
      (bass_input_naturality Q qF hpF hnF qG hpG hnG η hη) x

end KTheory.Bass.DiagramRowInterchange
