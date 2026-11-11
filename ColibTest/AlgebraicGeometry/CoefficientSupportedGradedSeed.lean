module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenSeedCompatibility

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open AlgebraicGeometry.Scheme.Modules CommRingCat.PolynomialLaurent
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientSupportedOpenZeroToGraded f T a).app S) :=
  boundedAboveFlatCoefficientSupportedOpenZeroToGraded_weak f T a S

example :
    boundedAboveFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) =
      boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T :=
  boundedAboveFlatCoefficientSupportedOpenBassSeed_restriction f T

variable [CompactSpace P.left] [CompactSpace Q.left]

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).unit a =
      boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a := rfl

example (a : Under R)
    (S : ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a).obj.Obj) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).obj
      ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation
        ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).map
          ((laurentUnderCoefficient R).app a))).app S) :=
  boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak f T a S

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedAboveFlatCoefficientSupportedGradedLaurentContraction f T a).level n
          (r, (t, x))) =
      (boundedAboveFlatCoefficientSupportedGradedLaurentContraction f T b).level n
        (r, (t, ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map
          n x)) :=
  boundedAboveFlatCoefficientSupportedGradedLaurentContraction_naturality f T g n r t x

example (a : Under R) :
    Homotopy (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap f T a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a)
        (parameterLooping (boundedAboveFlatCoefficientSupportedGradedOpenBassCone f T a))) :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassSeedNull f T a

example (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T).homotopy a).level n
      (r, x) =
      (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedNull f T a).level n (r, x) :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull_level f T a n r x

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
        (((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n
          (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy b).level n
        (s, ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).map g).map n x) :=
  boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull_coefficient f T g n s x

example :
    boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T) =
      boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T ≫
        boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T :=
  boundedAboveFlatCoefficientSupportedFullOpenBassSeed_grading f T

example (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a) :=
  boundedAboveFlatCoefficientSupportedOpenGradingNull_unitCompatible f T a

example (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s) =
      boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s ≫
        boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T :=
  boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice_seed f T s

example (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    Path.toContinuousMap
      ((boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).level n
        (s, (boundedAboveFlatCoefficientSupportedOpenBassSeedMap f T a).map n x)) t =
      Path.toContinuousMap ((boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap f T a).map
        n (((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n
          (s, x))) t :=
  boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed_apply f T a n s t x
