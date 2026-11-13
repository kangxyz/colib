module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStable
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (a : Under R)
example (d : ℤ) : Subsingleton (stableHomotopyGroup
    (mappingCone ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)) d) :=
  boundedAboveFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton f a d
example :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) :=
  boundedAboveFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence f a
