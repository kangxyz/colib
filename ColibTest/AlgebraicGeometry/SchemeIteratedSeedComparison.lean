module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedNullComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTelescope
open NaturalTrack GeometricSeedCospan NormalizedStageMap SchemeNaturalSeed
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    iteratedInputMap A B η hη ≫ iteratedTwistedTelescopeMap B =
      iteratedTwistedTelescopeMap A ≫ twistedInputMap A B η hη :=
  input_square A B η hη

example (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (D : Track laurent.op coefficient K)
    (a : F ⟶ G) (b : G ⟶ K) (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((iteratedTelescope A).obj X).space n) :
    ((iteratedTwistedTelescopeMap D).app X).map n
      (((iteratedInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((iteratedTwistedTelescopeMap A).app X).map n x) :=
  null_square A B D a b ha hb N hN X n r x

open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
example
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((iteratedTwistedTelescopeMap A).app X) :=
  model_iteratedTwistedTelescopeMap_stable M A X

end KTheory.Bass.SchemeIteratedSeedTelescope
