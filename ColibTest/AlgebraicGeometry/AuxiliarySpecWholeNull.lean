module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientNull
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterFiniteNull

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
noncomputable section
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example :
    (Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.enlargement f.left T) ≫
      Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.restriction f.left T)) ≫
        openComparison f T =
      fiberComparison f T ≫
        ((boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T ≫
          boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T) ≫
          boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T) :=
  fullComposite_model_square f T

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.fiber f.left T).obj
      (specUnder.obj a))).space n) :
    (prespectrumMap ((openComparison f T).app a)).map n
      (((ParameterAuxiliarySupport.fullNull f.left T).homotopy (specUnder.obj a)).level n
        (s, x)) =
      (prespectrumMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a)).map n
        (((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n
          (s, (prespectrumMap ((fiberComparison f T).app a)).map n x)) :=
  fullNull_coefficient_square f T a n s x

example (s : unitInterval) :
    Functor.whiskerLeft specUnder (parameterNullTimeSlice f T s) ≫
        Functor.whiskerRight (openComparison f T) prespectrumFunctor =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        coefficientFullNullTimeSlice f T s :=
  fullNull_timeSlice_square f T s

example (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
        i).app a).map n
      (((strictDiagramIterateNull squareFunctor (ParameterAuxiliarySupport.fullNull f.left T)
        i).homotopy (specUnder.obj a)).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a).map n
        (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level n
          (s, ((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
        i).app a).map n x)) :=
  finite_fullNull_square f T i a n s x

example (s : unitInterval) :
    ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor ⟶
      ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor :=
  parameterNullTimeSlice f T s

example (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T :=
  coefficientFullNullTimeSlice f T s
