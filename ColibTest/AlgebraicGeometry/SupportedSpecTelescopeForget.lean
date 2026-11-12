module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTelescope
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterTelescopeForget
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
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((telescopeIso f).hom.app a) := telescopeIso_stable f a
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
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fineTelescopeComparison f).app a) := fineTelescopeComparison_stable f a
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
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    Functor.whiskerLeft specUnder (ParameterFullCurrentNull.iteratedForget f.left) ≫
        GlobalParameterCoefficient.fineTelescopeComparison Q =
      fineTelescopeComparison f ≫ boundedAboveFlatCoefficientSupportedBassTelescopeForget f :=
        fineTelescope_forget_square f
end Test2
