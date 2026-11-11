/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Bass.DiagramRowIteration

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
noncomputable section
universe u v w

namespace ColibTest.FiniteRowInterchange
open KTheory.Bass KTheory.Bass.DiagramRowInterchange
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

example (X : C) (k : ℕ) : iterate Q 0 F q hp hn X k = q X k := rfl

example (i : ℕ) (X : C) (k : ℕ) :
    iterate Q (i + 1) F q hp hn X k =
      iterate Q i ((strictDiagramFunctor Q).obj F) (bass Q F q hp hn)
        (bass_point Q F q hp hn) (bass_naturality Q F q hp hn) X k := rfl

example (X : C) (k : ℕ) : iterate Q 1 F q hp hn X k = bass Q F q hp hn X k := rfl

example (i : ℕ) (X : C) (k : ℕ) :
    iterate Q i F q hp hn X k ((((strictDiagramIterate Q i).obj F).obj X).point (k + 3)) =
      (((strictDiagramIterate Q i).obj F).obj X).point (k + 3) :=
  iterate_point Q i F q hp hn X k

example (i : ℕ) {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) :
    iterate Q i F q hp hn Y k ((((strictDiagramIterate Q i).obj F).map g).map (k + 3) x) =
      (((strictDiagramIterate Q i).obj F).map g).map (k + 3)
        (iterate Q i F q hp hn X k x) :=
  iterate_naturality Q i F q hp hn g k x

example (i : ℕ)
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) (k : ℕ) (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 1))
    (s t : unitInterval) :
    iterate Q i F q hp hn X k ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 2)
      ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 1) x s) t) =
        (((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 2)
          ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 1) x t) s :=
  iterate_structure Q i F q hp hn hs X k x s t

example (X : C) (k : ℕ)
    (γ : Path (((ConeTrack.diagram Q F).obj X).point (k + 3))
      (((ConeTrack.diagram Q F).obj X).point (k + 3))) (r : unitInterval) :
    Path.toContinuousMap (bass Q F q hp hn X k γ) r = cone Q F q hp hn X k (γ r) := rfl

example (X : C) (k : ℕ) (t : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space (k + 3)) :
    cone Q F q hp hn X k
      ((StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level (k + 3)
        (t, x)) =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level (k + 3)
        (t, q (Q.obj X).left.left k x) := sourceNull Q F q hp hn X k t x

end ColibTest.FiniteRowInterchange

namespace ColibTest.FiniteRowParameter
open Topology.LoopPrespectrum.RowInterchange
variable {E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hp : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))

example (k : ℕ) (γ : Path (E.point (k + 3)) (E.point (k + 3))) (r : unitInterval) :
    Path.toContinuousMap (parameterLoop q hp k γ) r = q k (γ r) := rfl

example (k : ℕ) (hq : Function.Involutive (q k)) :
    Function.Involutive (parameterLoop q hp k) := parameterLoop_involutive q hp k hq

end ColibTest.FiniteRowParameter
