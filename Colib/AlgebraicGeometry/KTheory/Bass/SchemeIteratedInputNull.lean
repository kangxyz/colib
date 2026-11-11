/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.NormalizedDiagramNull
public import Colib.KTheory.Bass.StrictDiagramIndexTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTelescope
public import Colib.Topology.Prespectrum.TelescopeMapNullHomotopy

/-! # The original iterated-seed input maps and selected continuous null -/
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

/-- The literal original seed-iterate telescope. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:29"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
def iteratedTelescope (A : Track laurent.op coefficient F) :=
  StrictDiagramIndexChange.telescope squareFunctor (seed A)

/-- Original seed compatibility gives the literal finite input square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:33"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
theorem iteratedInput_transition (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) (i : ℕ) :
    (strictDiagramIterate squareFunctor i).map η ≫
        strictDiagramTransition squareFunctor (seed B) i =
      strictDiagramTransition squareFunctor (seed A) i ≫
        (strictDiagramIterate squareFunctor (i + 1)).map η :=
  (strictDiagramTransition_map squareFunctor (seed A) (seed B) η (seed_square A B η hη) i).symm

/-- The original iterated-seed input map with unchanged stage maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:42"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
def iteratedInputMap (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    iteratedTelescope A ⟶ iteratedTelescope B :=
  Telescope.diagramMap (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => (strictDiagramIterate squareFunctor i).obj G)
    (strictDiagramTransition squareFunctor (seed A))
    (strictDiagramTransition squareFunctor (seed B))
    (fun i => (strictDiagramIterate squareFunctor i).map η)
    (iteratedInput_transition A B η hη)

variable (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))

include hN

/-- The local two-time action equation gives the exact iterated null transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:63"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
theorem iteratedNull_transition (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((strictDiagramTransition squareFunctor (seed D) i).app X).map n
      (((strictDiagramIterateNull squareFunctor N
      i).homotopy X).level n (r, x)) =
      ((strictDiagramIterateNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((strictDiagramTransition squareFunctor (seed A) i).app X).map n x) := by
  have h := congrArg (fun η => (η.app X).map n x)
    (iteratedInput_transition A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) (hN r) i)
  rw [strictDiagramIterateNull_level, strictDiagramIterateNull_level]
  exact h

/-- Jointly continuous descent of the original iterated finite nulls. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:78"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
def iteratedInputNull : DiagramNullHomotopy
    (iteratedInputMap A B a ha) (iteratedInputMap B D b hb) where
  homotopy X := Telescope.mapNullHomotopy
    (fun i => ((strictDiagramIterate squareFunctor i).obj F).obj X) (fun i =>
      (strictDiagramTransition squareFunctor (seed A) i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).obj G).obj X) (fun i =>
      (strictDiagramTransition squareFunctor (seed B) i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).obj K).obj X) (fun i =>
      (strictDiagramTransition squareFunctor (seed D) i).app X)
    (fun i => ((strictDiagramIterate squareFunctor i).map a).app X) (fun i =>
      ((strictDiagramIterate squareFunctor i).map b).app X)
    (fun i => congrArg (fun η => η.app X) (iteratedInput_transition A B a ha i))
    (fun i => congrArg (fun η => η.app X) (iteratedInput_transition B D b hb i))
    (fun i => (strictDiagramIterateNull squareFunctor N i).homotopy X)
    (fun i n r x => iteratedNull_transition A D a b N hN i X n r x)
  naturality {X Y} f n r x := by
    induction x using Quot.inductionOn with
    | h z =>
      exact congrArg (fun y => Telescope.cylinder
        (fun i => ((strictDiagramIterate squareFunctor i).obj K).obj Y) (fun i =>
      (strictDiagramTransition squareFunctor (seed D) i).app Y)
        n z.1 (z.2.1, y)) ((strictDiagramIterateNull squareFunctor N z.1).naturality f n r z.2.2)

/-- The null time and telescope height remain independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedInputNull.lean:102"
  "adaptation" "Original iterated seed inputs and whole jointly continuous telescope null."]
theorem iteratedInputNull_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((iteratedInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed A) j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj K).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed D) j).app X) n i
        (t, ((strictDiagramIterateNull squareFunctor N i).homotopy X).level n (r, x)) := rfl

end KTheory.Bass.SchemeNaturalSeed
