module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopConeSeedPointwiseIdentification
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopSeedFactor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology LoopFactor
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) :
    HEq ((seed ((coneTrack A 1).loop)).app X)
      ((WholeSeedCospan.seed
        (GeometricSquareInterchange.geometricSquare
          ((strictDiagramFunctor squareFunctor).obj F))
        (bassTrack F A.homotopy A.naturality)
        (bassTrack_naturality F A.homotopy A.naturality)).app X) :=
  seed_loopCone_app_heq_bassSeed A X

example (A : Track laurent.op coefficient F) (X : Scheme.{u}ᵒᵖ) :
    (seed A.loop).app X ≫ parameterLoopingMap
        (coneStrength (F.mapArrow.mapArrow.obj (squareFunctor.obj X))) =
      parameterLoopingMap ((seed A).app X) ≫
        (LoopTranspose.iso ((ConeTrack.diagram squareFunctor F).obj X)).inv :=
  seed_loop_coneStrength A X

end KTheory.Bass.SchemeIteratedSeedTransition
