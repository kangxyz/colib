module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenChangeSeed
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
    (x : (prespectrum ((globalRow Q).obj a)).space n) :
    (prespectrumMap ((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction Q).track.homotopy a).level n (t, x)) =
    ((openLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((openRowChangeWeak f).app a)).map n x) :=
  openRowChangeWeak_track f a n t x

example :
    (globalLaurentAction Q).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor) =
    Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor ≫
      (openLaurentAction f).track.seed :=
  openRowChangeWeak_seed f

end
