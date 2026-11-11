module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTelescope
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.NaturalTrack KTheory.Bass.SchemeNaturalSeed
open KTheory.Bass.NormalizedStageMap KTheory.Bass.GeometricSeedCospan
universe u w
noncomputable section
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (η : F ⟶ G) (hη : Equivariant A B η)
example : currentTelescope A ⟶ currentTelescope B := currentInputMap A B η hη
example : normalizedTelescope A ⟶ normalizedTelescope B := normalizedInputMap A B η hη
example (i : ℕ) :
    (strictDiagramIterate squareFunctor i).map η ≫ currentTransition B i =
      currentTransition A i ≫ (strictDiagramIterate squareFunctor (i + 1)).map η :=
  currentInput_transition A B η hη i
example : currentInputMap A B η hη ≫ telescopeMap B =
    telescopeMap A ≫ normalizedInputMap A B η hη := telescopeMap_input_square A B η hη
