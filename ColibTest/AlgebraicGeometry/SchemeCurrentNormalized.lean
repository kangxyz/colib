/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageSquare
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan GeometricSquareInterchange SquareConeStrength
open LoopStrength LoopConeTrack IteratedLoopStrength FiniteLoopWords NormalizedStageMap
open FiniteParameterLooping
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    seed A ≫ (strictDiagramFunctor squareFunctor).map η = η ≫ seed B :=
  seed_square A B η hη

example (A : Track laurent.op coefficient F) :
    seed A.loop ≫ strengthDiagram squareFunctor F =
      Functor.whiskerRight (seed A) parameterLoopingFunctor :=
  seed_loop_strength A

example (A : Track laurent.op coefficient F) (j : ℕ) :
    seed (A.loops j) ≫ iteratedStrength squareFunctor j F = loopMap j (seed A) :=
  seed_iteratedStrength A j

example (A : Track laurent.op coefficient F) (i : ℕ) :
    Track laurent.op coefficient (FiniteConeTopology.iterate squareFunctor i F) :=
  coneTrack A i

example (A : Track laurent.op coefficient F) (i : ℕ) :
    normalized squareFunctor i F ⟶ normalized squareFunctor (i + 1) F :=
  normalizedTransition A i

example (A : Track laurent.op coefficient F) (i : ℕ) :
    currentTransition A i ≫ stageMap squareFunctor (i + 1) F =
      stageMap squareFunctor i F ≫ normalizedTransition A i :=
  currentTransition_stageMap A i

end KTheory.Bass.SchemeNaturalSeed
end
