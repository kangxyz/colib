module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull
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

example (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedTransition D i).app X).map n (((normalizedNull squareFunctor N i).homotopy
      X).level n (r, x)) =
      ((normalizedNull squareFunctor N (i + 1)).homotopy X).level n
        (r, ((twistedTransition A i).app X).map n x) :=
  twistedNull_transition A D a b N hN i X n r x

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ)
    (r t : unitInterval) (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
      (r, Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (twistedTransition A j).app X) n i (t, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j K).obj X)
        (fun j => (twistedTransition D j).app X) n i
        (t, ((normalizedNull squareFunctor N i).homotopy X).level n (r, x)) :=
  twistedInputNull_cylinder A B D a b ha hb N hN X n i r t x

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope A).obj X).space n) :
    ((conjugacyTelescopeMap D).app X).map n
      (((normalizedInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((conjugacyTelescopeMap A).app X).map n x) :=
  conjugacyTelescopeMap_null A B D a b ha hb N hN X n r x

end KTheory.Bass.SchemeNaturalSeed
