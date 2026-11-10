/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Bass.DiagramRowRefinementHomotopy

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
noncomputable section
universe u v w

namespace ColibTest.RowRefinementBase
open Topology.LoopPrespectrum.RowRefinement
variable (E : LoopPrespectrum.{u})
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))

example (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (r s : unitInterval) :
    rowStructure E q hq k γ r s = q k (E.structureMap (k + 2) (γ s) r) := rfl

example (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (r : unitInterval) :
    rowStructure E q hq k γ r = basedLoopMap (evaluation E q k r)
      (evaluation_point E q hq k r) γ := by apply structure_row

example : (spectrum E q hq).structureMap 0 = ContinuousMap.id _ := rfl

variable (hswap : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
  q k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
    E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)

example (k : ℕ) :
    (comparison E q hq hswap).map (k + 1) = E.structureMap (k + 1) := rfl

example (x : E.space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((comparison E q hq hswap).map 0 x) r) s =
      E.structureMap 1 (E.structureMap 0 x r) s := rfl

end ColibTest.RowRefinementBase

namespace ColibTest.RowRefinementHomotopy
open Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  {a b : E ⟶ F}
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
  (hb : ∀ k x, qF k (b.map (k + 3) x) = b.map (k + 3) (qE k x))
  (H : Homotopy a b)
  (hH : ∀ k t x, qF k (H.level (k + 3) (t, x)) =
    H.level (k + 3) (t, qE k x))

example (k : ℕ)
    (γ : Path (E.point (k + 2)) (E.point (k + 2))) (t r : unitInterval) :
    Path.toContinuousMap ((homotopy qE qF hE hF ha hb H hH).level (k + 1) (t, γ)) r =
      H.level (k + 2) (t, γ r) := rfl

example
    (γ : Path (Path.refl (E.point 2)) (Path.refl (E.point 2))) (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((homotopy qE qF hE hF ha hb H hH).level 0 (t, γ)) r) s =
      H.level 2 (t, γ r s) := rfl

example
    (hz : ∀ k x, qF k ((zeroHom E F).map (k + 3) x) =
      (zeroHom E F).map (k + 3) (qE k x)) :
    map qE qF hE hF (zeroHom E F) hz = zeroHom (spectrum E qE hE) (spectrum F qF hF) := by
  apply Topology.LoopPrespectrum.RowRefinement.map_zero

end ColibTest.RowRefinementHomotopy

namespace ColibTest.RowRefinementDiagram
open KTheory.Bass.DiagramRowRefinement
variable {C : Type u} [Category.{v} C] {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (pF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (nF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (pG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (nG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))

variable (θ : F ⟶ G)
  (hθ : ∀ X k x, qG X k ((θ.app X).map (k + 3) x) =
    (θ.app X).map (k + 3) (qF X k x))
  (H : ∀ X, Homotopy (η.app X) (θ.app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) n t x,
    (G.map g).map n ((H X).level n (t, x)) =
      (H Y).level n (t, (F.map g).map n x))
  (hrow : ∀ X k t x, qG X k ((H X).level (k + 3) (t, x)) =
    (H X).level (k + 3) (t, qF X k x))

example {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (γ : ((diagram F qF pF nF).obj X).space n) :
    ((diagram G qG pG nG).map g).map n
        ((homotopy qF pF nF qG pG nG η hη θ hθ H hrow X).level n (t, γ)) =
      (homotopy qF pF nF qG pG nG η hη θ hθ H hrow Y).level n
        (t, ((diagram F qF pF nF).map g).map n γ) := by
  apply homotopy_naturality
  exact hH

end ColibTest.RowRefinementDiagram

namespace ColibTest.RowRefinementMaps
open Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (a : E ⟶ F)
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))

example (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (s : unitInterval) :
    Path.toContinuousMap ((map qE qF hE hF a ha).map (k + 1) γ) s =
      a.map (k + 2) (γ s) := rfl

example (γ : Path (Path.refl (E.point 2)) (Path.refl (E.point 2)))
    (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((map qE qF hE hF a ha).map 0 γ) r) s = a.map 2 (γ r s) := rfl

variable
  (hsE : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
    qE k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
      E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)
  (hsF : ∀ k (x : F.space (k + 1)) (s t : unitInterval),
    qF k (F.structureMap (k + 2) (F.structureMap (k + 1) x s) t) =
      F.structureMap (k + 2) (F.structureMap (k + 1) x t) s)

example :
    a ≫ comparison F qF hF hsF = comparison E qE hE hsE ≫ map qE qF hE hF a ha := by
  apply comparison_naturality

end ColibTest.RowRefinementMaps
