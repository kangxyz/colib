module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationFiniteNull
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

example (s : unitInterval) :
    globalSupportedOpenNullTimeSlice f s ≫
      Functor.whiskerRight (openRowRestriction f) prespectrumFunctor =
    Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s :=
  globalSupportedOpenNull_timeSlice f s

example (i : ℕ) (a : Under R) (n : ℕ)
    (s : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
      (supportedRow f ⋙ prespectrumFunctor)).obj a).space n) :
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a).map n
      (((globalSupportedOpenFiniteNull f i).homotopy a).level n (s, x)) =
    ((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level n
      (s, (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a).map n x) :=
  globalSupportedOpenFiniteNull_restriction f i a n s x


end
