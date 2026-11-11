/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundaryHomotopy

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w

namespace Topology.LoopPrespectrum.RefinedNullSeed
section
variable {E D C D' C' : LoopPrespectrum.{u}} (f : E ⟶ D) (j : D ⟶ C)
  (r : D ⟶ D') (s : C ⟶ C') (j' : D' ⟶ C') (h : r ≫ j' = j ≫ s)
  (K : Homotopy (f ≫ r) (f ≫ r)) (N : Homotopy (f ≫ j) (zeroHom E C))

example : Homotopy ((f ≫ j) ≫ s) ((f ≫ j) ≫ s) :=
  cell f j r s j' h K

example (H : Homotopy f f) (hK : K = H.postcomp r) :
    seed f j r s j' h K N = (H.postcomp j).nullLoopMap N ≫ parameterLoopingMap s :=
  seed_eq f j r s j' h K N H hK

end
end Topology.LoopPrespectrum.RefinedNullSeed

namespace Topology.LoopPrespectrum.RowRefinement
section
variable {D E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (a : E ⟶ F)
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
  (f : D ⟶ spectrum E qE hE) (H : Homotopy f f)

example (k : ℕ) (x : D.space (k + 1)) (t s : unitInterval) :
    a.map (k + 2) (normalizedStage qE hE f H k x t s) =
      normalizedStage qF hF (f ≫ map qE qF hE hF a ha)
        (H.postcomp (map qE qF hE hF a ha)) k x t s :=
  normalizedStage_postcomp qE qF hE hF a ha f H k x t s

example :
    normalizedOperation qE hE f H ≫ parameterLoopingMap (map qE qF hE hF a ha) =
      normalizedOperation qF hF (f ≫ map qE qF hE hF a ha)
        (H.postcomp (map qE qF hE hF a ha)) :=
  normalizedOperation_postcomp qE qF hE hF a ha f H

end
end Topology.LoopPrespectrum.RowRefinement

namespace KTheory.Bass.DiagramRowSeed
section
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

example (X : C) :
    cornerComparison Q F q hp hs X ≫ inclusion Q F q hp hn X =
      mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))) ≫
        comparison Q F q hp hn hs X :=
  comparison_inclusion Q F q hp hn hs X

end
end KTheory.Bass.DiagramRowSeed

namespace KTheory.Bass.DiagramRowSeed
section
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
variable (X : C)
  (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
    (diagonal Q F X ≫ cornerComparison Q F q hp hs X))

example :
    Homotopy (normalizedBoundary Q F q hp hn hs X K) (seed Q F q hp hn hs X K) :=
  normalizedBoundaryHomotopy Q F q hp hn hs X K

end
end KTheory.Bass.DiagramRowSeed
