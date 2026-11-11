module
import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.GeometricSeedCospan
open GeometricSquareInterchange WholeSeedCospan
open SquareConeStrength HomotopyWord


variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (coefficient.app X)) (F.map (coefficient.app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map (laurent.op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

example (r : unitInterval) :
    diagramHomotopyAt (sourceTrack F H) (sourceTrack_naturality F H hH) r =
      diagramHomotopyAt (η := Functor.whiskerRight coefficient F)
        (θ := Functor.whiskerRight coefficient F) H hH r :=
  sourceTrack_timeSlice F H hH r

example : Natural (bassTrack F H hH) :=
  bassTrack_naturality F H hH

example (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (bassTrack F H hH X).at r ≫
        (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X =
      (strictDiagramMapHomotopy (sourceTrack F H) (sourceTrack_naturality F H hH)
        squareFunctor X).at r :=
  wholeUnitSquare F H hH X r

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor squareFunctor).obj F).obj X).space n) :
    ((chiGeom F).app X).map n
        ((sourceNull (geometricSquare ((strictDiagramFunctor squareFunctor).obj F)) X).level n
          (r,x)) =
      (strictDiagramMapHomotopy (sourceNull (geometricSquare F))
        (sourceNull_naturality (geometricSquare F)) squareFunctor X).level n (r,x) :=
  chiGeom_sourceNull F X n r x

example (X : Scheme.{u}ᵒᵖ) :
    (WholeSeedCospan.seed
      (geometricSquare ((strictDiagramFunctor squareFunctor).obj F))
      (bassTrack F H hH) (bassTrack_naturality F H hH)).app X ≫
        parameterLoopingMap ((chiGeom F).app X) =
      (((strictDiagramFunctor squareFunctor).map
        (WholeSeedCospan.seed (geometricSquare F) (sourceTrack F H)
          (sourceTrack_naturality F H hH))).app X) ≫
        LoopStrength.strength squareFunctor
          (mappingConeDiagram (comparison (geometricSquare F))) X :=
  seed_cospan F H hH X

end KTheory.Bass.GeometricSeedCospan
