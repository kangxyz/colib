module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeComparison
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeSquares
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeNull

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

open GeometricSeedCospan ParameterLaurentTrack

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((fiberTelescopeComparison f T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.fiberAction f.left T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed j).app a) n i
      (s, ((fiberFiniteComparison f T i).app a).map n x) :=
  fiberTelescopeComparison_cylinder f T a n i s x

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fiberTelescopeComparison f T).app a) :=
  fiberTelescopeComparison_stable f T a

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((ambientTelescopeComparison Q T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.ambientAction T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed j).app a)
          n i
      (s, ((ambientFiniteComparison Q T i).app a).map n x) :=
  ambientTelescopeComparison_cylinder Q T a n i s x

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((ambientTelescopeComparison Q T).app a) :=
  ambientTelescopeComparison_stable Q T a

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.openAction f.left T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed j).app a) n i
      (s, ((openFiniteComparison f T i).app a).map n x) :=
  openTelescopeComparison_cylinder f T a n i s x

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((openTelescopeComparison f T).app a) :=
  openTelescopeComparison_stable f T a

example (i : ℕ) :
    Functor.whiskerLeft specUnder ((strictDiagramIterate squareFunctor i).map
        (ParameterAuxiliarySupport.firstMap f.left T)) ≫ ambientFiniteComparison Q T i =
      fiberFiniteComparison f T i ≫ boundedAboveFlatCoefficientSupportedFiberBassForget f T i :=
  finite_enlargement_square f T i

example (i : ℕ) :
    Functor.whiskerLeft specUnder ((strictDiagramIterate squareFunctor i).map
        (ParameterAuxiliarySupport.secondMap f.left T)) ≫ openFiniteComparison f T i =
      ambientFiniteComparison Q T i ≫
        (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
          boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i) :=
  finite_restriction_square f T i

example :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.iteratedEnlargement f.left T) ≫
        ambientTelescopeComparison Q T =
      fiberTelescopeComparison f T ≫
        boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T :=
  telescope_enlargement_square f T

example :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.iteratedRestriction f.left T) ≫
        openTelescopeComparison f T =
      ambientTelescopeComparison Q T ≫
        (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T ≫
          boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T) :=
  telescope_restriction_square f T

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope
      (ParameterAuxiliarySupport.fiberAction f.left T)).obj (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (((ParameterAuxiliarySupport.iteratedNull f.left T).homotopy
        (specUnder.obj a)).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (s, ((fiberTelescopeComparison f T).app a).map n x) :=
  telescope_fullNull_square f T a n s x

example : specUnder ⋙
    SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.fiberAction f.left T) ⟶
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T :=
  fiberTelescopeComparison f T

example : specUnder ⋙
    SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.ambientAction T) ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor (Q := Q) T :=
  ambientTelescopeComparison Q T

example : specUnder ⋙
    SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.openAction f.left T) ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  openTelescopeComparison f T
