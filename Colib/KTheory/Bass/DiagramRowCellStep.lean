/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowCellBass

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

/-- The next original coefficient and computed row comparison fix the actual cell endpoints. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:53-57"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def nextInput :=
  Functor.whiskerRight c ((strictDiagramFunctor Q).obj F) ≫
    Functor.whiskerLeft L (bassComparison F q hp hn hs Q)

/-- Only the endpoint witnesses are transported; the independently descended cell is unchanged. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:58-69"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def step (X : C) :
    Homotopy ((nextInput L c F q hp hn hs Q).app X)
      ((nextInput L c F q hp hn hs Q).app X) :=
  (rawBass L c F q hp hn hs H hH Q χ X).cast
    (by simpa only [Homotopy.at_zero_eq, nextInput, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using
      rawBass_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X 0)
    (by simpa only [Homotopy.at_one_eq, nextInput, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using
      rawBass_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X 1)

/-- Endpoint transport does not alter any level, cell time, row time or old-loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:70-74"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem step_level (X : C) (n : ℕ) :
    (step L c F q hp hn hs H hH Q χ A hcell hχ X).level n =
      (rawBass L c F q hp hn hs H hH Q χ X).level n := rfl

/-- The actual normalized next cell has the proved whole original action comparison. -/
@[colib_tag "COL-0525", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:75-88"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem step_at_eq (X : C) (t : unitInterval) :
    (step L c F q hp hn hs H hH Q χ A hcell hχ X).at t =
      ((A.bass Q χ hχ).homotopy X).at t ≫
        (bassComparison F q hp hn hs Q).app (L.obj X) := by
  have he : (step L c F q hp hn hs H hH Q χ A hcell hχ X).at t =
      (rawBass L c F q hp hn hs H hH Q χ X).at t := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  exact he.trans (rawBass_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X t)

/-- The original next action time slice, with both coefficient endpoints fixed explicitly. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:89-96"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def originalNextTimeSlice (t : unitInterval) :=
  diagramHomotopyAt
    (η := Functor.whiskerRight c ((strictDiagramFunctor Q).obj F))
    (θ := Functor.whiskerRight c ((strictDiagramFunctor Q).obj F))
    (A.bass Q χ hχ).homotopy (A.bass Q χ hχ).naturality t ≫
  Functor.whiskerLeft L (bassComparison F q hp hn hs Q)

/-- The constructed next cells form a natural transformation at every original time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:97-109"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def stepTimeSlice (t : unitInterval) :
    (strictDiagramFunctor Q).obj F ⟶
      L ⋙ DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn) where
  app X := (step L c F q hp hn hs H hH Q χ A hcell hχ X).at t
  naturality {X Y} g := by
    rw [step_at_eq L c F q hp hn hs H hH Q χ A hcell hχ X,
      step_at_eq L c F q hp hn hs H hH Q χ A hcell hχ Y]
    exact (originalNextTimeSlice L c F q hp hn hs Q χ A hχ t).naturality g

/-- The next whole cell satisfies actual index naturality without adding an assumption. -/
@[colib_tag "COL-0525", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellStep.lean:110-125"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem step_naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    ((DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
      (DiagramRowInterchange.bass Q F q hp hn)
      (DiagramRowInterchange.bass_point Q F q hp hn)
      (DiagramRowInterchange.bass_naturality Q F q hp hn)).map (L.map g)).map n
        ((step L c F q hp hn hs H hH Q χ A hcell hχ X).level n (t, x)) =
      (step L c F q hp hn hs H hH Q χ A hcell hχ Y).level n
        (t, (((strictDiagramFunctor Q).obj F).map g).map n x) :=
  (congrArg (fun f : ((strictDiagramFunctor Q).obj F).obj X ⟶
      (DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn)).obj (L.obj Y) => f.map n x)
    ((stepTimeSlice L c F q hp hn hs H hH Q χ A hcell hχ t).naturality g)).symm

end KTheory.Bass.DiagramRowCell
