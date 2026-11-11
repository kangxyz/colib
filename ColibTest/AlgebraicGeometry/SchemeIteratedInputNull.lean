/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedInputNull
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F) : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  iteratedTelescope A

example (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) (i : ℕ) :
    (strictDiagramIterate squareFunctor i).map η ≫
        strictDiagramTransition squareFunctor (seed B) i =
      strictDiagramTransition squareFunctor (seed A) i ≫
        (strictDiagramIterate squareFunctor (i + 1)).map η :=
  iteratedInput_transition A B η hη i

example (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    iteratedTelescope A ⟶ iteratedTelescope B :=
  iteratedInputMap A B η hη

variable (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))

include hN

example (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((strictDiagramTransition squareFunctor (seed D) i).app X).map n
      (((strictDiagramIterateNull squareFunctor N
      i).homotopy X).level n (r, x)) =
      ((strictDiagramIterateNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((strictDiagramTransition squareFunctor (seed A) i).app X).map n x) :=
  iteratedNull_transition A D a b N hN i X n r x

example : DiagramNullHomotopy
    (iteratedInputMap A B a ha) (iteratedInputMap B D b hb) :=
  iteratedInputNull A B D a b ha hb N hN

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((iteratedInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed A) j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj K).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed D) j).app X) n i
        (t, ((strictDiagramIterateNull squareFunctor N i).homotopy X).level n (r, x)) :=
  iteratedInputNull_cylinder A B D a b ha hb N hN X n i r t x

end KTheory.Bass.SchemeNaturalSeed
end
