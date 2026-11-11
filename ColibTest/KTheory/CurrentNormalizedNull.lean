module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull
open CategoryTheory Topology Opposite AlgebraicGeometry
open Topology.LoopPrespectrum Topology.LoopPrespectrum.FiniteParameterLooping
open Topology.LoopPrespectrum.FiniteLoopWords
open KTheory.Bass KTheory.Bass.NaturalTrack KTheory.Bass.NormalizedStageMap
open KTheory.Bass.SchemeNaturalSeed
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
noncomputable section
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (D : Track laurent.op coefficient K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
example (i : ℕ) : DiagramNullHomotopy (loopMap i a) (loopMap i b) := loopsNull N i
example (Q : Scheme.{u}ᵒᵖ ⥤ Arrow (Arrow Scheme.{u}ᵒᵖ)) (i : ℕ) :
    DiagramNullHomotopy (normalizedMap Q i a) (normalizedMap Q i b) := normalizedNull Q N i
example : DiagramNullHomotopy (currentInputMap A B a ha) (currentInputMap B D b hb) :=
  currentInputNull A B D a b ha hb N hN
example : DiagramNullHomotopy (normalizedInputMap A B a ha) (normalizedInputMap B D b hb) :=
  normalizedInputNull A B D a b ha hb N hN
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope A).obj X).space n) :
    ((telescopeMap D).app X).map n
      (((currentInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((normalizedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((telescopeMap A).app X).map n x) := telescopeMap_null A B D a b ha hb N hN X n r x
