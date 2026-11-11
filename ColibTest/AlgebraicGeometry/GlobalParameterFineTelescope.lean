module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
universe u
noncomputable section
variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

example : specUnder ⋙ ParameterModels.ambient Q.left ≅ globalRow Q :=
  parameterRowModelIso Q

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterRowModelIso Q).hom.app a =
      boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op :=
  parameterRowModelIso_hom_app Q a

example : specUnder ⋙ parameterDiagram Q ≅ globalRow Q ⋙ prespectrumFunctor :=
  rowSpectrumIso Q

example : Functor.whiskerLeft specUnder
      (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) ≫
    (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare
      (parameterDiagram Q)).hom ≫
    (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowSpectrumIso Q).hom =
      (rowSpectrumIso Q).hom ≫ (globalLaurentAction Q).track.seed :=
  seed_square_row Q

example (i : ℕ) :
    specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q) ≅
      globalDiagram Q i :=
  finiteIso Q i

example : specUnder ⋙ parameterTelescope Q.left ≅ globalTelescope Q :=
  telescopeIso Q

example : (telescopeIso Q).hom ≫ (telescopeIso Q).inv =
    𝟙 (specUnder ⋙ parameterTelescope Q.left) :=
  (telescopeIso Q).hom_inv_id

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fineTelescopeComparison Q).app a =
      (telescopeIso Q).hom.app a ≫ (telescopeRestriction Q).app a := rfl

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((fineTelescopeComparison Q).app a)) :=
  fineTelescopeComparison_stable Q a _
