module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStages
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules CommRingCat.PolynomialLaurent
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example (i : ℕ) (a : Under R) : IsStableEquivalence
    (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a)) :=
  boundedAboveFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence f i a
example (i : ℕ) : boundedAboveFlatCoefficientOpenBassTelescopeInclusion f i ≫
    boundedAboveFlatCoefficientOpenBassTelescopeRestriction f =
      boundedAboveFlatCoefficientOpenBassRestriction f i ≫
        boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion f i :=
  boundedAboveFlatCoefficientOpenBassTelescopeInclusion_restriction f i
example (a : Under R) : IsStableEquivalence
    (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)) :=
  boundedAboveFlatCoefficientOpenBassTelescopeRestriction_coneFiber_isStableEquivalence f a
