module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationNullSeed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) :
    TrackInterchange ((globalSupportedOpenNull f).homotopy a)
      ((globalSupportedOpenNull f).homotopy ((laurentUnderFunctor R).obj a))
      ((supportedLaurentAction f).track.homotopy a)
      ((openLaurentAction f).track.homotopy a) :=
  globalSupportedOpenNull_laurentInterchange f a

example (i : ℕ) (a : Under R) (n : ℕ)
    (s : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
      (supportedRow f ⋙ prespectrumFunctor)).obj a).space n) :
    ((globalSupportedOpenFiniteNull f (i + 1)).homotopy a).level n
      (s, ((strictDiagramTransition (laurentUnderSquareFunctor R)
        (supportedLaurentAction f).track.seed i).app a).map n x) =
    ((strictDiagramTransition (laurentUnderSquareFunctor R)
      (openLaurentAction f).track.seed i).app a).map n
        (((globalSupportedOpenFiniteNull f i).homotopy a).level n (s, x)) :=
  globalSupportedOpenFiniteNull_transition f i a n s x

end
