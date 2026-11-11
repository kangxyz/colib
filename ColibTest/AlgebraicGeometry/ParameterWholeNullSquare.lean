module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterTelescopeNull
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

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj
      (specUnder.obj a)).space n) :
    ((telescopeIso P).hom.app a).map n
      (((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).level n
        (s, x)) =
      ((FullOpenTelescope.null f).homotopy a).level n
        (s, ((GlobalSupportedParameterCoefficient.telescopeIso f).hom.app a).map n x) :=
          telescope_fullNull_square f a n s x
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

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj
      (specUnder.obj a)).space n) :
    ((fineTelescopeComparison P).app a).map n
      (((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).level n
        (s, x)) =
      ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level n
        (s, ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a).map n x) :=
          telescope_fullNull_fine_square f a n s x
end Test1
