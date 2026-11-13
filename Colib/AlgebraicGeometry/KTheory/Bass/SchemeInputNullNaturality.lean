/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull

/-!
# Whole original input-null squares on current telescopes

A same-time square of original diagram nulls propagates through the actual
finite Bass functor and the original current telescope. The null time and
cylinder height remain independent, and all original input maps are retained.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass

/-- Every actual finite Bass iterate preserves the same original null time square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNullNaturality.lean:25"
  "adaptation" "Original input maps preserve composition, identities and whole null squares."]
theorem strictDiagramIterateNull_square {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C))
    {F G K F' G' K' : C ⥤ LoopPrespectrum.{w}}
    {a : F ⟶ G} {b : G ⟶ K} {a' : F' ⟶ G'} {b' : G' ⟶ K'}
    (N : DiagramNullHomotopy a b) (N' : DiagramNullHomotopy a' b')
    (α : F ⟶ F') (γ : K ⟶ K')
    (h : ∀ X n r x, (γ.app X).map n ((N.homotopy X).level n (r, x)) =
      (N'.homotopy X).level n (r, (α.app X).map n x))
    (i : ℕ) (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space n) :
    (((strictDiagramIterate Q i).map γ).app X).map n
        (((strictDiagramIterateNull Q N i).homotopy X).level n (r, x)) =
      ((strictDiagramIterateNull Q N' i).homotopy X).level n
        (r, (((strictDiagramIterate Q i).map α).app X).map n x) := by
  have ht : diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r ≫ γ =
      α ≫ diagramHomotopyAt (η := a' ≫ b') (θ := diagramZeroMap F' K')
        N'.homotopy N'.naturality r := by
    apply NatTrans.ext
    funext Y
    apply Topology.LoopPrespectrum.Hom.ext
    funext m
    apply ContinuousMap.ext
    intro y
    exact h Y m r y
  have hh := congrArg (strictDiagramIterate Q i).map ht
  simp only [Functor.map_comp] at hh
  rw [strictDiagramIterateNull_level, strictDiagramIterateNull_level]
  exact congrArg (fun k => (k.app X).map n x) hh

namespace SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
variable {F G K F' G' K' : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K)
    (A' : Track laurent.op coefficient F') (B' : Track laurent.op coefficient G')
    (D' : Track laurent.op coefficient K')
    (a : F ⟶ G) (b : G ⟶ K) (a' : F' ⟶ G') (b' : G' ⟶ K')
    (ha : Equivariant A B a) (hb : Equivariant B D b)
    (ha' : Equivariant A' B' a') (hb' : Equivariant B' D' b')
    (N : DiagramNullHomotopy a b) (N' : DiagramNullHomotopy a' b')
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
    (hN' : ∀ r, Equivariant A' D'
      (diagramHomotopyAt (η := a' ≫ b') (θ := diagramZeroMap F' K')
        N'.homotopy N'.naturality r))
    (α : F ⟶ F') (γ : K ⟶ K')
    (hα : Equivariant A A' α) (hγ : Equivariant D D' γ)
    (h : ∀ X n r x, (γ.app X).map n ((N.homotopy X).level n (r, x)) =
      (N'.homotopy X).level n (r, (α.app X).map n x))

include h in
/-- The full current-telescope null retains the original square and every original time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputNullNaturality.lean:79"
  "adaptation" "Original input maps preserve composition, identities and whole null squares."]
theorem currentInputNull_naturality (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope A).obj X).space n) :
    ((currentInputMap D D' γ hγ).app X).map n
        (((currentInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((currentInputNull A' B' D' a' b' ha' hb' N' hN').homotopy X).level n
        (r, ((currentInputMap A A' α hα).app X).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun j => ((strictDiagramIterate squareFunctor j).obj K').obj X)
      (fun j => (currentTransition D' j).app X) n z.1 (z.2.1, y))
      (strictDiagramIterateNull_square squareFunctor N N' α γ h z.1 X n r z.2.2)

end SchemeNaturalSeed
end KTheory.Bass
