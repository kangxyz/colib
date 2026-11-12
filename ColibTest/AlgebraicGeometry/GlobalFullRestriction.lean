module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenModels
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescope
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescopeSquare
noncomputable section
namespace Test0
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    globalOpenRestriction f ≫ rowRestriction P =
      openRowRestriction f ≫ boundedAboveFlatCoefficientOpenRestrictionModelTransformation f :=
        globalOpenRestriction_square f
end Test0

namespace Test1
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

example (i : ℕ) :
    finiteRestriction f i ≫ globalTransition P i =
      OpenTelescope.globalTransition f i ≫ finiteRestriction f (i + 1) :=
        finiteRestriction_transition f i
end Test1

namespace Test2
open CategoryTheory Topology AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open CommRingCat.PolynomialLaurent KTheory.Bass Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

example :
    restriction f ≫ telescopeRestriction P =
      OpenTelescope.telescopeRestriction f ≫
        boundedAboveFlatCoefficientOpenBassTelescopeRestriction f := restriction_square f
end Test2
