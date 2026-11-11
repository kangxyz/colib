/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedInputMaps
public import Colib.Topology.Prespectrum.TelescopeMapNullHomotopy

/-! # The original normalized null through the fixed-word telescope conjugacy -/
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

/-- The local two-time action equation gives the exact twisted null transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedNull.lean:37"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem twistedNull_transition (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedTransition D i).app X).map n (((normalizedNull squareFunctor N i).homotopy
      X).level n (r, x)) =
      ((normalizedNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((twistedTransition A i).app X).map n x) := by
  have h := congrArg (fun η => (η.app X).map n x)
    (twistedInput_transition A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r) (hN r) i)
  have h₀ := congrArg (fun η => (η.app X).map n x)
    (normalizedNull_timeSlice squareFunctor N i r)
  have h₁ := congrArg (fun η => (η.app X).map n
    (((twistedTransition A i).app X).map n x))
    (normalizedNull_timeSlice squareFunctor N (i + 1) r)
  exact (congrArg (((twistedTransition D i).app X).map n) h₀).trans
    (h.trans h₁.symm)

/-- Jointly continuous descent of the original twisted finite nulls. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedNull.lean:56"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedInputNull : DiagramNullHomotopy
    (twistedInputMap A B a ha) (twistedInputMap B D b hb) where
  homotopy X := Telescope.mapNullHomotopy
    (fun i => (normalized squareFunctor i F).obj X) (fun i => (twistedTransition A i).app X)
    (fun i => (normalized squareFunctor i G).obj X) (fun i => (twistedTransition B i).app X)
    (fun i => (normalized squareFunctor i K).obj X) (fun i => (twistedTransition D i).app X)
    (fun i => (normalizedMap squareFunctor i a).app X) (fun i => (normalizedMap squareFunctor
      i b).app X)
    (fun i => congrArg (fun η => η.app X) (twistedInput_transition A B a ha i))
    (fun i => congrArg (fun η => η.app X) (twistedInput_transition B D b hb i))
    (fun i => (normalizedNull squareFunctor N i).homotopy X)
    (fun i n r x => twistedNull_transition A D a b N hN i X n r x)
  naturality {X Y} f n r x := by
    induction x using Quot.inductionOn with
    | h z =>
      exact congrArg (fun y => Telescope.cylinder
        (fun i => (normalized squareFunctor i K).obj Y) (fun i => (twistedTransition D i).app Y)
        n z.1 (z.2.1, y)) ((normalizedNull squareFunctor N z.1).naturality f n r z.2.2)

/-- The null time and telescope height remain independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedNull.lean:76"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem twistedInputNull_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (twistedTransition A j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j K).obj X)
        (fun j => (twistedTransition D j).app X) n i
        (t, ((normalizedNull squareFunctor N i).homotopy X).level n (r, x)) := rfl

omit hN in
/-- The actual finite conjugacy preserves the original normalized null at every time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedNull.lean:87"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem conjugatingIso_null (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((conjugatingIso i K).hom.app X).map n
      (((normalizedNull squareFunctor N i).homotopy X).level n (r, x)) =
      ((normalizedNull squareFunctor N i).homotopy X).level n
        (r, ((conjugatingIso i F).hom.app X).map n x) := by
  have h := congrArg (fun η => (η.app X).map n x)
    (conjugatingIso_naturality i
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
  have h₀ := congrArg (fun η => (η.app X).map n x)
    (normalizedNull_timeSlice squareFunctor N i r)
  have h₁ := congrArg (fun η => (η.app X).map n
    (((conjugatingIso i F).hom.app X).map n x))
    (normalizedNull_timeSlice squareFunctor N i r)
  exact (congrArg (((conjugatingIso i K).hom.app X).map n) h₀).trans
    (h.trans h₁.symm)

/-- The fixed-word telescope map preserves the entire original continuous null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedNull.lean:106"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem conjugacyTelescopeMap_null (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope A).obj X).space n) :
    ((conjugacyTelescopeMap D).app X).map n
      (((normalizedInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((conjugacyTelescopeMap A).app X).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (normalized squareFunctor i K).obj X)
      (fun i => (twistedTransition D i).app X) n z.1 (z.2.1, y))
      (conjugatingIso_null a b N z.1 X n r z.2.2)

end KTheory.Bass.SchemeNaturalSeed

namespace KTheory.Bass.SchemeNaturalSeed

attribute [colib_tag "COL-0574"] conjugacyTelescopeMap_null

end KTheory.Bass.SchemeNaturalSeed
