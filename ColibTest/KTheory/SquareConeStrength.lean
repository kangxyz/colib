module
import Colib.KTheory.Bass.SquareConeStrength
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.SquareConeStrength
open PushoutStrength PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]

example (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) :
    left S.left.hom S.hom.left ≫ comparison S = S.hom.right :=
  left_comparison S

variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) (Q : C ⥤ Arrow (Arrow C))
example :
    rho S.left.hom S.hom.left Q ≫ (strictDiagramFunctor Q).map (comparison S) =
      comparison (bassSquare S Q) :=
  rho_comparison S Q

example (X : C) :
    mappingConeInclusion ((comparison (bassSquare S Q)).app X) ≫ (chi S Q).app X =
      (((strictDiagramFunctor Q).map (coneInclusion (comparison S))).app X) :=
  chi_inclusion S Q X

example (X : C) (n : ℕ) (r : unitInterval)
    (x : ((pushout (bassSquare S Q).left.hom (bassSquare S Q).hom.left).obj X).space n) :
    ((chi S Q).app X).map n
      ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n (r, x)) =
    (((strictDiagramFunctor Q).map
      (diagramHomotopyAt (coneNull (comparison S))
        (coneNull_naturality (comparison S)) r)).app X).map n
          ((rho S.left.hom S.hom.left Q).app X |>.map n x) :=
  chi_cylinder S Q X n r x

example (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj S.left.left).obj X).space n) :
    ((chi S Q).app X).map n ((sourceNull (bassSquare S Q) X).level n (r, x)) =
      (strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).level n (r, x) :=
  chi_sourceNull S Q X n r x

end KTheory.Bass.SquareConeStrength
