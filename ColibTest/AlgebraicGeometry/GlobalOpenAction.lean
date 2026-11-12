module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenAction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism
universe u
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((openRow f).obj a)).space n) :
    (prespectrumMap ((openRowRestriction f).app ((laurentUnderFunctor R).obj a))).map n
      (((openLaurentAction f).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((openRowRestriction f).app a)).map n x) :=
  openRowRestriction_track f a n t x

example :
    (openLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (openRowRestriction f) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientOpenLaurentAction f).track.seed :=
  openRowRestriction_seed f

end
