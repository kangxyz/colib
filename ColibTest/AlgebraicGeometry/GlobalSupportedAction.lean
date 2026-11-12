module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedForgetSeed
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open CommRingCat.PolynomialLaurent KTheory.Bass
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
example (a : Under R) :
    Preserves ((supportedRowForget f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((supportedLaurentAction f).unit a) ((globalLaurentAction Q).unit a) :=
  supportedRowForget_unit f a
example : (supportedLaurentAction f).track.seed ≫
    (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
      (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor) =
    Functor.whiskerRight (supportedRowForget f) prespectrumFunctor ≫
      (globalLaurentAction Q).track.seed := supportedRowForget_seed f

example (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((supportedRowRestriction f).app ((laurentUnderFunctor R).obj a))).map n
      (((supportedLaurentAction f).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((supportedRowRestriction f).app a)).map n x)  :=
  supportedRowRestriction_track f a n t x

example :
    (supportedLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientSupportedLaurentAction f).track.seed  :=
  supportedRowRestriction_seed f
