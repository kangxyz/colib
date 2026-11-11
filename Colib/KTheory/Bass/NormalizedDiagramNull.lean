/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.ConeDiagramNull
public import Colib.KTheory.Bass.NormalizedStageNaturality
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-! # The original continuous null through finite cone and loop normalization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.NormalizedStageMap
open FiniteConeTopology FiniteLoopWords
variable {C : Type u} [Category.{v} C]
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}

/-- Loop the original continuous diagram null, keeping its same homotopy time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:27"
  "adaptation" "Original whole null, independent times and exact comparison."]
def loopNull (N : DiagramNullHomotopy a b) :
    DiagramNullHomotopy (Functor.whiskerRight a parameterLoopingFunctor)
      (Functor.whiskerRight b parameterLoopingFunctor) where
  homotopy X := (N.homotopy X).parameterLoopingNull
  naturality {X Y} f n r x := by
    change Path ((F.obj X).point n) ((F.obj X).point n) at x
    apply Path.ext
    funext t
    exact N.naturality f n r (x t)

/-- Finite looping applies the original whole null at every independent loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:38"
  "adaptation" "Original whole null, independent times and exact comparison."]
def loopsNull (N : DiagramNullHomotopy a b) :
    ∀ i, DiagramNullHomotopy (loopMap i a) (loopMap i b)
  | 0 => N
  | i + 1 => loopNull (loopsNull N i)

/-- Each finite loop time slice is the literal finite loop of the original null time slice. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:44"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem loopsNull_timeSlice (N : DiagramNullHomotopy a b) (i : ℕ) (r : unitInterval) :
    diagramHomotopyAt (η := loopMap i a ≫ loopMap i b)
        (θ := diagramZeroMap (loopDiagram i F) (loopDiagram i K))
        (loopsNull N i).homotopy (loopsNull N i).naturality r =
      loopMap i (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    apply NatTrans.ext
    funext X
    have h := congrArg (fun η => η.app X) ih
    exact (Homotopy.parameterLooping_at ((loopsNull N i).homotopy X) r).trans
      (congrArg parameterLoopingMap h)

/-- Iterate the original unlooped cone null without selecting new tracks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:60"
  "adaptation" "Original whole null, independent times and exact comparison."]
def conesNull (Q : C ⥤ Arrow (Arrow C)) (N : DiagramNullHomotopy a b) :
    ∀ i, DiagramNullHomotopy (iterateMap Q i a) (iterateMap Q i b)
  | 0 => N
  | i + 1 => ConeTrack.diagramNull Q (conesNull Q N i)

/-- Each finite cone null time slice is the original finite cone map of that time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:66"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem conesNull_timeSlice (Q : C ⥤ Arrow (Arrow C)) (N : DiagramNullHomotopy a b)
    (i : ℕ) (r : unitInterval) :
    diagramHomotopyAt (η := iterateMap Q i a ≫ iterateMap Q i b)
        (θ := diagramZeroMap (iterate Q i F) (iterate Q i K))
        (conesNull Q N i).homotopy (conesNull Q N i).naturality r =
      iterateMap Q i (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    apply NatTrans.ext
    funext X
    exact (ConeTrack.diagramNull_at Q (conesNull Q N i) X r).trans
      (congrArg (fun η => (ConeTrack.map Q η).app X) ih)

/-- The normalized finite-stage null is exactly i original cones and then i original loops. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:82"
  "adaptation" "Original whole null, independent times and exact comparison."]
def normalizedNull (Q : C ⥤ Arrow (Arrow C)) (N : DiagramNullHomotopy a b) (i : ℕ) :
    DiagramNullHomotopy (normalizedMap Q i a) (normalizedMap Q i b) :=
  loopsNull (conesNull Q N i) i

/-- All original null times survive the complete normalized construction. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:87"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem normalizedNull_timeSlice (Q : C ⥤ Arrow (Arrow C)) (N : DiagramNullHomotopy a b)
    (i : ℕ) (r : unitInterval) :
    diagramHomotopyAt (η := normalizedMap Q i a ≫ normalizedMap Q i b)
        (θ := diagramZeroMap (normalized Q i F) (normalized Q i K))
        (normalizedNull Q N i).homotopy (normalizedNull Q N i).naturality r =
      normalizedMap Q i (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) :=
  (loopsNull_timeSlice (conesNull Q N i) i r).trans
    (congrArg (loopMap i) (conesNull_timeSlice Q N i r))

/-- The existing finite stage comparison preserves the complete selected original null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedDiagramNull.lean:98"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem stageMap_null (Q : C ⥤ Arrow (Arrow C)) (N : DiagramNullHomotopy a b)
    (i : ℕ) (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space n) :
    ((stageMap Q i K).app X).map n (((strictDiagramIterateNull Q N i).homotopy X).level n (r, x)) =
      ((normalizedNull Q N i).homotopy X).level n
        (r, ((stageMap Q i F).app X).map n x) := by
  rw [strictDiagramIterateNull_level]
  have h := congrArg (fun η => (η.app X).map n x)
    (stageMap_naturality Q i
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
  have ht := congrArg (fun η => (η.app X).map n (((stageMap Q i F).app X).map n x))
    (normalizedNull_timeSlice Q N i r)
  exact h.trans ht.symm

end KTheory.Bass.NormalizedStageMap

namespace KTheory.Bass.NormalizedStageMap

attribute [colib_tag "COL-0567"] stageMap_null

end KTheory.Bass.NormalizedStageMap
