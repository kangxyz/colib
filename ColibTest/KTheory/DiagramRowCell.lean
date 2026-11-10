/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowCellStep

/-! # Independent cone descent of a natural cell into a genuine row refinement

The input is a whole cross-diagram cell, not a Model structure on the later spectrum.
Its four actual corners descend through the original square cone, inverse geometric index,
and forward row strength. The source-null height remains independent of the cell time.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


variable
  (H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
    ((input L c F q hp hn hs).app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
    ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
      ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x))

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)


variable (A : NaturalTrack.Track L c F)
  (hcell : ∀ X t, (H X).at t = (A.homotopy X).at t ≫
    (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X))
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

example (S : Arrow (Arrow C)) (n : ℕ) (r s : unitInterval)
    (x : (F.obj S.left.left).space n) :
    (square L c F q hp hn hs H hH S).cone.level n
        (r, (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj S)).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy
        ((L ⋙ DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj S)).level n
          (s, (H S.left.left).level n (r, x)) := by
  exact square_sourceNull L c F q hp hn hs H hH S n r s x

example (X : C) (n : ℕ) (r s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (cone L c F q hp hn hs H hH Q χ X).level n
        (r, (StrictSquare.sourceNullHomotopy
          (F.mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (DiagramConeRowStrength.strength Q F q hp hn (L.obj X)).map n
        ((StrictSquare.sourceNullHomotopy
          ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj
            (Q.obj (L.obj X)))).level n
          (s, ((DiagramRowRefinement.diagram F q hp hn).map (χ.inv.app X).left.left).map n
            ((H (Q.obj X).left.left).level n (r, x)))) := by
  exact cone_sourceNull L c F q hp hn hs H hH Q χ X n r s x

example (t : unitInterval) :
    diagramHomotopyAt (η := input L c F q hp hn hs)
        (θ := input L c F q hp hn hs) H hH t =
      diagramHomotopyAt (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
        A.homotopy A.naturality t ≫
      Functor.whiskerLeft L (DiagramRowRefinement.comparison F q hp hn hs) := by
  exact timeSlice_eq L c F q hp hn hs H hH A hcell t

example (X : C) (t : unitInterval) :
    (cone L c F q hp hn hs H hH Q χ X).at t =
      (ConeTrack.map Q (diagramHomotopyAt (η := input L c F q hp hn hs)
        (θ := input L c F q hp hn hs) H hH t)).app X ≫
      ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X ≫
        DiagramConeRowStrength.strength Q F q hp hn (L.obj X)) := by
  exact cone_at L c F q hp hn hs H hH Q χ X t

example (X : C) (t : unitInterval) :
    (cone L c F q hp hn hs H hH Q χ X).at t =
      ((A.cone Q χ hχ).homotopy X).at t ≫
        coneComparison F q hp hn hs Q (L.obj X) := by
  exact cone_at_eq L c F q hp hn hs H hH A hcell Q χ hχ X t

example (X : C) :
    parameterLoopingMap (coneComparison F q hp hn hs Q X) ≫
        loopRowInverse F q hp hn Q X =
      (bassComparison F q hp hn hs Q).app X := by
  exact loopRow_comparison F q hp hn hs Q X

example (X : C) (t : unitInterval) :
    (rawBass L c F q hp hn hs H hH Q χ X).at t =
      ((A.bass Q χ hχ).homotopy X).at t ≫
        (bassComparison F q hp hn hs Q).app (L.obj X) := by
  exact rawBass_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X t

example (X : C) (n : ℕ) :
    (step L c F q hp hn hs H hH Q χ A hcell hχ X).level n =
      (rawBass L c F q hp hn hs H hH Q χ X).level n := by
  exact step_level L c F q hp hn hs H hH Q χ A hcell hχ X n

example (X : C) (t : unitInterval) :
    (step L c F q hp hn hs H hH Q χ A hcell hχ X).at t =
      ((A.bass Q χ hχ).homotopy X).at t ≫
        (bassComparison F q hp hn hs Q).app (L.obj X) := by
  exact step_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X t

example {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    ((DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
      (DiagramRowInterchange.bass Q F q hp hn)
      (DiagramRowInterchange.bass_point Q F q hp hn)
      (DiagramRowInterchange.bass_naturality Q F q hp hn)).map (L.map g)).map n
        ((step L c F q hp hn hs H hH Q χ A hcell hχ X).level n (t, x)) =
      (step L c F q hp hn hs H hH Q χ A hcell hχ Y).level n
        (t, (((strictDiagramFunctor Q).obj F).map g).map n x) := by
  exact step_naturality L c F q hp hn hs H hH Q χ A hcell hχ g n t x

end KTheory.Bass.DiagramRowCell
