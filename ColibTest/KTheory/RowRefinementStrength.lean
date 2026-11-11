/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Bass.DiagramConeRowStrengthHomotopy
import Colib.KTheory.Bass.DiagramBassRowStrength

open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open scoped Topology unitInterval
noncomputable section
universe u v w

namespace ColibTest.RowStrengthPart0
open Topology.LoopPrespectrum.RowRefinement
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (qA : ∀ k, C(A.space (k + 3), A.space (k + 3)))
  (qB : ∀ k, C(B.space (k + 3), B.space (k + 3)))
  (qC : ∀ k, C(C.space (k + 3), C.space (k + 3)))
  (hA : ∀ k, qA k (A.point (k + 3)) = A.point (k + 3))
  (hB : ∀ k, qB k (B.point (k + 3)) = B.point (k + 3))
  (hC : ∀ k, qC k (C.point (k + 3)) = C.point (k + 3))
  (hf : ∀ k x, qB k (f.map (k + 3) x) = f.map (k + 3) (qA k x))
  (hg : ∀ k x, qC k (g.map (k + 3) x) = g.map (k + 3) (qA k x))

example :
    HomotopyPushout.inl (map qA qB hA hB f hf) (map qA qC hA hC g hg) ≫
      pushoutStrength f g qA qB qC hA hB hC hf hg =
        pushoutLeft f g qA qB qC hA hB hf hg := by
  apply Topology.LoopPrespectrum.RowRefinement.pushoutStrength_left

example :
    HomotopyPushout.inr (map qA qB hA hB f hf) (map qA qC hA hC g hg) ≫
      pushoutStrength f g qA qB qC hA hB hC hf hg =
        pushoutRight f g qA qB qC hA hB hC hf hg := by
  apply Topology.LoopPrespectrum.RowRefinement.pushoutStrength_right

example (k : ℕ) (t s : unitInterval)
    (γ : Path (A.point (k + 2)) (A.point (k + 2))) :
    Path.toContinuousMap ((pushoutStrength f g qA qB qC hA hB hC hf hg).map (k + 1)
      (HomotopyPushout.cylinder (map qA qB hA hB f hf) (map qA qC hA hC g hg)
        (k + 1) (t, γ))) s = HomotopyPushout.cylinder f g (k + 2) (t, γ s) := by
  apply Topology.LoopPrespectrum.RowRefinement.pushoutStrength_overlap_succ

example (t r s : unitInterval)
    (γ : Path (Path.refl (A.point 2)) (Path.refl (A.point 2))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((pushoutStrength f g qA qB qC hA hB hC hf hg).map 0
        (HomotopyPushout.cylinder (map qA qB hA hB f hf) (map qA qC hA hC g hg)
          0 (t, γ))) r) s = HomotopyPushout.cylinder f g 2 (t, γ r s) := by
  apply Topology.LoopPrespectrum.RowRefinement.pushoutStrength_overlap_zero

end ColibTest.RowStrengthPart0

namespace ColibTest.RowStrengthPart1
open Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (hf : ∀ k x, qF k (f.map (k + 3) x) = f.map (k + 3) (qE k x))

example :
    mappingConeInclusion (map qE qF hE hF f hf) ≫ coneStrength f qE qF hE hF hf =
      coneInclusion f qE qF hE hF hf := by
  apply Topology.LoopPrespectrum.RowRefinement.coneStrength_inclusion

example (k : ℕ) (t s : unitInterval)
    (γ : Path (E.point (k + 2)) (E.point (k + 2))) :
    Path.toContinuousMap ((coneStrength f qE qF hE hF hf).map (k + 1)
      ((mappingConeHomotopy (map qE qF hE hF f hf)).level (k + 1) (t, γ))) s =
      (mappingConeHomotopy f).level (k + 2) (t, γ s) := by
  apply Topology.LoopPrespectrum.RowRefinement.coneStrength_cylinder_succ

example (t r s : unitInterval)
    (γ : Path (Path.refl (E.point 2)) (Path.refl (E.point 2))) :
    Path.toContinuousMap (Path.toContinuousMap ((coneStrength f qE qF hE hF hf).map 0
      ((mappingConeHomotopy (map qE qF hE hF f hf)).level 0 (t, γ))) r) s =
      (mappingConeHomotopy f).level 2 (t, γ r s) := by
  apply Topology.LoopPrespectrum.RowRefinement.coneStrength_cylinder_zero

end ColibTest.RowStrengthPart1

namespace ColibTest.RowStrengthPart2
open KTheory.Bass.DiagramConeRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

example {X Y : C} (g : X ⟶ Y) :
    (ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn)).map g ≫
        strength Q F q hp hn Y =
      strength Q F q hp hn X ≫
        RowRefinement.map (DiagramRowInterchange.cone Q F q hp hn X)
          (DiagramRowInterchange.cone Q F q hp hn Y)
          (DiagramRowInterchange.cone_point Q F q hp hn X)
          (DiagramRowInterchange.cone_point Q F q hp hn Y)
          ((ConeTrack.diagram Q F).map g)
          (DiagramRowInterchange.cone_naturality Q F q hp hn g) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_naturality

example
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) :
    (ConeTrack.map Q (DiagramRowRefinement.comparison F q hp hn hs)).app X ≫
        strength Q F q hp hn X =
      RowRefinement.comparison ((ConeTrack.diagram Q F).obj X)
        (DiagramRowInterchange.cone Q F q hp hn X)
        (DiagramRowInterchange.cone_point Q F q hp hn X)
        (DiagramRowInterchange.cone_structure Q F q hp hn hs X) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_comparison

example (X : C) (k : ℕ) (t s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).left.left).point (k + 2))
      ((F.obj (Q.obj X).left.left).point (k + 2))) :
    Path.toContinuousMap ((strength Q F q hp hn X).map (k + 1)
      ((StrictSquare.sourceNullHomotopy
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X))).level
          (k + 1) (t, γ))) s =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level
        (k + 2) (t, γ s) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_sourceNull_succ

example (X : C) (t r s : unitInterval)
    (γ : Path (Path.refl ((F.obj (Q.obj X).left.left).point 2))
      (Path.refl ((F.obj (Q.obj X).left.left).point 2))) :
    Path.toContinuousMap (Path.toContinuousMap ((strength Q F q hp hn X).map 0
      ((StrictSquare.sourceNullHomotopy
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X))).level
          0 (t, γ))) r) s =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level
        2 (t, γ r s) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_sourceNull_zero

end ColibTest.RowStrengthPart2

namespace ColibTest.RowStrengthPart3
open KTheory.Bass.DiagramConeRowStrength
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
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))
  (θ : F ⟶ G)
  (hθ : ∀ X k x, qG X k ((θ.app X).map (k + 3) x) =
    (θ.app X).map (k + 3) (qF X k x))
  (H : ∀ X, Homotopy (η.app X) (θ.app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) n t x,
    (G.map g).map n ((H X).level n (t, x)) =
      (H Y).level n (t, (F.map g).map n x))
  (hrow : ∀ X k t x, qG X k ((H X).level (k + 3) (t, x)) =
    (H X).level (k + 3) (t, qF X k x))

example (X : C) (k : ℕ) (t s : unitInterval)
    (x : (source Q F qF pF nF X).space (k + 1)) :
    Path.toContinuousMap ((strength Q G qG pG nG X).map (k + 1)
      ((rowConeHomotopy Q qF pF nF qG pG nG η hη θ hθ H hH hrow X).level (k + 1)
        (t, x))) s =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level (k + 2)
        (t, Path.toContinuousMap ((strength Q F qF pF nF X).map (k + 1) x) s) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_homotopy_succ

example (X : C) (t r s : unitInterval)
    (x : (source Q F qF pF nF X).space 0) :
    Path.toContinuousMap (Path.toContinuousMap ((strength Q G qG pG nG X).map 0
      ((rowConeHomotopy Q qF pF nF qG pG nG η hη θ hθ H hH hrow X).level 0
        (t, x))) r) s =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level 2
        (t, Path.toContinuousMap (Path.toContinuousMap
          ((strength Q F qF pF nF X).map 0 x) r) s) := by
  apply KTheory.Bass.DiagramConeRowStrength.strength_homotopy_zero

end ColibTest.RowStrengthPart3

namespace ColibTest.RowStrengthPart4
open Topology.LoopPrespectrum.RowRefinement
variable (E : LoopPrespectrum.{u})
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))

example (k : ℕ)
    (γ : Path (Path.refl (E.point (k + 2))) (Path.refl (E.point (k + 2))))
    (t s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((parameterLoopingComparison E q hq).map (k + 1) γ) t) s = γ s t := by
  apply Topology.LoopPrespectrum.RowRefinement.parameterLoopingComparison_succ

example
    (γ : Path (Path.refl (Path.refl (E.point 2))) (Path.refl (Path.refl (E.point 2))))
    (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((parameterLoopingComparison E q hq).map 0 γ) t) r) s = γ r s t := by
  apply Topology.LoopPrespectrum.RowRefinement.parameterLoopingComparison_zero

end ColibTest.RowStrengthPart4

namespace ColibTest.RowStrengthPart5
open KTheory.Bass.DiagramBassRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

example (X : C) (k : ℕ)
    (γ : Path ((DiagramConeRowStrength.source Q F q hp hn X).point (k + 1))
      ((DiagramConeRowStrength.source Q F q hp hn X).point (k + 1))) (s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((strength Q F q hp hn X).map (k + 1) γ) s) t =
      Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
        (γ t)) s := by
  apply KTheory.Bass.DiagramBassRowStrength.strength_succ

example (X : C)
    (γ : Path ((DiagramConeRowStrength.source Q F q hp hn X).point 0)
      ((DiagramConeRowStrength.source Q F q hp hn X).point 0)) (r s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((strength Q F q hp hn X).map 0 γ) r) s) t =
      Path.toContinuousMap (Path.toContinuousMap
        ((DiagramConeRowStrength.strength Q F q hp hn X).map 0 (γ t)) r) s := by
  apply KTheory.Bass.DiagramBassRowStrength.strength_zero

example {X Y : C} (g : X ⟶ Y) :
    (source Q F q hp hn).map g ≫ strength Q F q hp hn Y =
      strength Q F q hp hn X ≫ (target Q F q hp hn).map g := by
  apply KTheory.Bass.DiagramBassRowStrength.strength_naturality

example
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) :
    (((strictDiagramFunctor Q).map (DiagramRowRefinement.comparison F q hp hn hs)).app X) ≫
        strength Q F q hp hn X =
      (DiagramRowRefinement.comparison ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn) (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn)
        (DiagramRowInterchange.bass_structure Q F q hp hn hs)).app X := by
  apply KTheory.Bass.DiagramBassRowStrength.strength_comparison

end ColibTest.RowStrengthPart5
