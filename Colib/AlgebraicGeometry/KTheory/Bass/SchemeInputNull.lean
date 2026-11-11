/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.NormalizedDiagramNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTelescope
public import Colib.Topology.Prespectrum.TelescopeMapNullHomotopy

/-! # Original whole nulls on current and normalized seed telescopes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))

include hN

/-- The local two-time action equation gives the exact current null transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:37"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem currentNull_transition (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((currentTransition D i).app X).map n (((strictDiagramIterateNull squareFunctor N
      i).homotopy X).level n (r, x)) =
      ((strictDiagramIterateNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((currentTransition A i).app X).map n x) := by
  have h := congrArg (fun η => (η.app X).map n x)
    (currentInput_transition A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) (hN r) i)
  rw [strictDiagramIterateNull_level, strictDiagramIterateNull_level]
  exact h

/-- Jointly continuous descent of the original current finite nulls. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:51"
  "adaptation" "Original whole null, independent times and exact comparison."]
def currentInputNull : DiagramNullHomotopy
    (currentInputMap A B a ha) (currentInputMap B D b hb) where
  homotopy X := Telescope.mapNullHomotopy
    (fun i => ((strictDiagramIterate squareFunctor i).obj F).obj X) (fun i =>
      (currentTransition A i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).obj G).obj X) (fun i =>
      (currentTransition B i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).obj K).obj X) (fun i =>
      (currentTransition D i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).map a).app X) (fun i =>
      ((strictDiagramIterate squareFunctor i).map b).app X)
    (fun i => congrArg (fun η => η.app X) (currentInput_transition A B a ha i))
    (fun i => congrArg (fun η => η.app X) (currentInput_transition B D b hb i))
    (fun i => (strictDiagramIterateNull squareFunctor N i).homotopy X)
    (fun i n r x => currentNull_transition A D a b N hN i X n r x)
  naturality {X Y} f n r x := by
    induction x using Quot.inductionOn with
    | h z =>
      exact congrArg (fun y => Telescope.cylinder
        (fun i => ((strictDiagramIterate squareFunctor i).obj K).obj Y) (fun i =>
      (currentTransition D i).app Y)
        n z.1 (z.2.1, y)) ((strictDiagramIterateNull squareFunctor N z.1).naturality f n r z.2.2)

/-- The null time and telescope height remain independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:75"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem currentInputNull_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((currentInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (currentTransition A j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj K).obj X)
        (fun j => (currentTransition D j).app X) n i
        (t, ((strictDiagramIterateNull squareFunctor N i).homotopy X).level n (r, x)) := rfl

/-- The local two-time action equation gives the exact normalized null transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:85"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem normalizedNull_transition (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((normalizedTransition D i).app X).map n (((normalizedNull squareFunctor N i).homotopy
      X).level n (r, x)) =
      ((normalizedNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((normalizedTransition A i).app X).map n x) := by
  have h := congrArg (fun η => (η.app X).map n x)
    (normalizedInput_transition A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) (hN r) i)
  have h₀ := congrArg (fun η => (η.app X).map n x)
    (normalizedNull_timeSlice squareFunctor N i r)
  have h₁ := congrArg (fun η => (η.app X).map n
    (((normalizedTransition A i).app X).map n x))
    (normalizedNull_timeSlice squareFunctor N (i + 1) r)
  exact (congrArg (((normalizedTransition D i).app X).map n) h₀).trans
    (h.trans h₁.symm)

/-- Jointly continuous descent of the original normalized finite nulls. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:104"
  "adaptation" "Original whole null, independent times and exact comparison."]
def normalizedInputNull : DiagramNullHomotopy
    (normalizedInputMap A B a ha) (normalizedInputMap B D b hb) where
  homotopy X := Telescope.mapNullHomotopy
    (fun i => (normalized squareFunctor i F).obj X) (fun i => (normalizedTransition A i).app X)
    (fun i => (normalized squareFunctor i G).obj X) (fun i => (normalizedTransition B i).app X)
    (fun i => (normalized squareFunctor i K).obj X) (fun i => (normalizedTransition D i).app X)
    (fun i => (normalizedMap squareFunctor i a).app X) (fun i => (normalizedMap squareFunctor
      i b).app X)
    (fun i => congrArg (fun η => η.app X) (normalizedInput_transition A B a ha i))
    (fun i => congrArg (fun η => η.app X) (normalizedInput_transition B D b hb i))
    (fun i => (normalizedNull squareFunctor N i).homotopy X)
    (fun i n r x => normalizedNull_transition A D a b N hN i X n r x)
  naturality {X Y} f n r x := by
    induction x using Quot.inductionOn with
    | h z =>
      exact congrArg (fun y => Telescope.cylinder
        (fun i => (normalized squareFunctor i K).obj Y) (fun i => (normalizedTransition D i).app Y)
        n z.1 (z.2.1, y)) ((normalizedNull squareFunctor N z.1).naturality f n r z.2.2)

/-- The null time and telescope height remain independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:124"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem normalizedInputNull_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((normalizedInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (normalizedTransition A j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j K).obj X)
        (fun j => (normalizedTransition D j).app X) n i
        (t, ((normalizedNull squareFunctor N i).homotopy X).level n (r, x)) := rfl

/-- The unchanged stage comparison preserves the entire continuous telescope null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNull.lean:134"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem telescopeMap_null (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope A).obj X).space n) :
    ((telescopeMap D).app X).map n
      (((currentInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((normalizedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((telescopeMap A).app X).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (normalized squareFunctor i K).obj X)
      (fun i => (normalizedTransition D i).app X) n z.1 (z.2.1, y))
      (stageMap_null squareFunctor N z.1 X n r z.2.2)

end KTheory.Bass.SchemeNaturalSeed
