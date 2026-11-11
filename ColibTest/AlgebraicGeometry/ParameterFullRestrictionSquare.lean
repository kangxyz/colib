module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineRestrictionSquare
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionTelescopeSquare
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterIteratedOpenIdentification
noncomputable section
namespace Test0
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    parameterRestrictionMap f = ParameterFullCurrentNull.fullMap f.left :=
      parameterRestrictionMap_eq_fullMap f
end Test0

namespace Test1
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    Functor.whiskerLeft specUnder (parameterTelescopeRestriction f) ≫ (telescopeIso P).hom =
      (telescopeIso Q).hom ≫ LocalizationTelescope.openMap f ≫
        FullOpenTelescope.restriction f := fullRestriction_telescope_square f
end Test1

namespace Test2
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    Functor.whiskerLeft specUnder (parameterTelescopeRestriction f) ≫
        fineTelescopeComparison P =
      fineTelescopeComparison Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeOpen f ≫
        boundedAboveFlatCoefficientOpenBassTelescopeRestriction f := fine_fullRestriction_square f
end Test2
