module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedLaurentContraction
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedSeedCompatibility

open CategoryTheory AlgebraicGeometry Topology Opposite
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

example : LaurentSeed.ModelAction (boundedAboveFlatCoefficientGradedOpenModelFunctor f) :=
  boundedAboveFlatCoefficientGradedOpenLaurentAction f

example : boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f ⟶
    (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f) :=
  boundedAboveFlatCoefficientGradedOpenBassSeed f

example (a : Under R)
    (S : ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).obj a).obj.Obj) :
    ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).obj
      ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).map
        ((laurentUnderCoefficient R).app a))).app S) :=
  boundedAboveFlatCoefficientGradedLaurentZero_weak f a S

example
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedAboveFlatCoefficientGradedLaurentContraction f a).level n (r, (t, x))) =
      (boundedAboveFlatCoefficientGradedLaurentContraction f b).level n
        (r, (t, ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n x)) :=
  boundedAboveFlatCoefficientGradedLaurentContraction_naturality f g n r t x

example (a : Under R) :
    LoopPrespectrum.Homotopy (boundedAboveFlatCoefficientGradedOpenBassSeedMap f a)
      (zeroHom ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a)
        (parameterLooping (boundedAboveFlatCoefficientGradedOpenBassCone f a))) :=
  boundedAboveFlatCoefficientGradedOpenBassSeedNull f a

example (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull f).homotopy a).level n (r, x) =
      (boundedAboveFlatCoefficientGradedOpenBassSeedNull f a).level n (r, x) :=
  boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull_level f a n r x

example (a : Under R) :
    Preserves
      ((boundedAboveFlatCoefficientOpenGradingModelTransformation f).app
        ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((boundedAboveFlatCoefficientFullOpenLaurentAction f).unit a)
      ((boundedAboveFlatCoefficientGradedOpenLaurentAction f).unit a) :=
  boundedAboveFlatCoefficientOpenGrading_laurentUnit f a

example :
    boundedAboveFlatCoefficientFullOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f) =
      boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientGradedOpenBassSeed f :=
  boundedAboveFlatCoefficientFullOpenBassSeed_grading f

example
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves
      (((boundedAboveFlatCoefficientOpenRestrictionModelTransformation f).app a ≫
        (boundedAboveFlatCoefficientOpenGradingModelTransformation f).app a).hom.toFunctor)
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r))
      (boundedAboveFlatCoefficientSectionUnitIso (op P, a)
        (boundedAboveFlatCoefficientUnit (op P, a) r)) :=
  boundedAboveFlatCoefficientOpenComposite_unit_preserves f a r

example (a : Under R) :
    TrackInterchange
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientOpenLaurentHomotopy f a)
      (boundedAboveFlatCoefficientGradedOpenLaurentHomotopy f a) :=
  boundedAboveFlatCoefficientOpenGradingNull_laurentInterchange f a

example (s : unitInterval) :
    boundedAboveFlatCoefficientOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s) =
      boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s ≫
        boundedAboveFlatCoefficientGradedOpenBassSeed f :=
  boundedAboveFlatCoefficientOpenGradingNullTimeSlice_seed f s

example (a : Under R) (s : unitInterval) :
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s)).app a :=
  boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_at f a s

example
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedAboveFlatCoefficientOpenBassSeedMap f a).map n x) =
      (boundedAboveFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) :=
  boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_seed f a n s x

example
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    Path.toContinuousMap ((boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedAboveFlatCoefficientOpenBassSeedMap f a).map n x)) t =
      Path.toContinuousMap ((boundedAboveFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x))) t :=
  boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_seed_apply f a n s t x

