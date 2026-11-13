/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowInputNaturality
public import Colib.KTheory.Bass.DiagramRowHomotopy
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice

/-! # Original null time slices preserve every finite row interchange

The original iterated null is used literally. Its time-slice formula retains the successor
casts and lets the existing input naturality theorem propagate the whole row square.
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
  {M : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ M} {b : M ⟶ G}
  (H : DiagramNullHomotopy a b)
  (hrow : ∀ X k r x, qG X k ((H.homotopy X).level (k + 3) (r, x)) =
    (H.homotopy X).level (k + 3) (r, qF X k x))

include hrow

/-- Every original finite null retains its time and both actual iterated row actions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNull.lean:41"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem iterate_null (i : ℕ) (X : C) (k : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) :
    iterate Q i G qG hpG hnG X k
        (((strictDiagramIterateNull Q H i).homotopy X).level (k + 3) (r, x)) =
      ((strictDiagramIterateNull Q H i).homotopy X).level (k + 3)
        (r, iterate Q i F qF hpF hnF X k x) := by
  rw [strictDiagramIterateNull_level, strictDiagramIterateNull_level]
  exact iterate_input_naturality Q qF hpF hnF qG hpG hnG
    (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F G)
      H.homotopy H.naturality r)
    (fun X k x => hrow X k r x) i X k x

/-- Its original moving cone keeps null time independent of every quotient height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNull.lean:54"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem cone_iterate_null (i : ℕ) (X : C) (k : ℕ) (r : unitInterval)
    (x : ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj F)).obj X).space (k + 3)) :
    cone Q ((strictDiagramIterate Q i).obj G)
        (iterate Q i G qG hpG hnG) (iterate_point Q i G qG hpG hnG)
        (iterate_naturality Q i G qG hpG hnG) X k
        ((diagramSquareMapHomotopy
          (η := (strictDiagramIterate Q i).map a ≫ (strictDiagramIterate Q i).map b)
          (θ := diagramZeroMap ((strictDiagramIterate Q i).obj F)
            ((strictDiagramIterate Q i).obj G))
          (strictDiagramIterateNull Q H i).homotopy
          (strictDiagramIterateNull Q H i).naturality (Q.obj X)).cone.level (k + 3) (r, x)) =
      (diagramSquareMapHomotopy
          (η := (strictDiagramIterate Q i).map a ≫ (strictDiagramIterate Q i).map b)
          (θ := diagramZeroMap ((strictDiagramIterate Q i).obj F)
            ((strictDiagramIterate Q i).obj G))
          (strictDiagramIterateNull Q H i).homotopy
        (strictDiagramIterateNull Q H i).naturality (Q.obj X)).cone.level (k + 3)
        (r, cone Q ((strictDiagramIterate Q i).obj F)
          (iterate Q i F qF hpF hnF) (iterate_point Q i F qF hpF hnF)
          (iterate_naturality Q i F qF hpF hnF) X k x) :=
  cone_homotopy Q _ _ _ _ _ _
    (η := (strictDiagramIterate Q i).map a ≫ (strictDiagramIterate Q i).map b)
    (θ := diagramZeroMap ((strictDiagramIterate Q i).obj F)
      ((strictDiagramIterate Q i).obj G)) (strictDiagramIterateNull Q H i).homotopy
    (strictDiagramIterateNull Q H i).naturality
    (iterate_null Q qF hpF hnF qG hpG hnG H hrow i) X k r x

end KTheory.Bass.DiagramRowInterchange
