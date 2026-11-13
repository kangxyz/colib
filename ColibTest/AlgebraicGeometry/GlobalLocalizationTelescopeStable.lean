module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeStable
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) : IsStableEquivalence
    ((SupportedTelescope.telescopeRestriction f).app a) :=
  SupportedTelescope.telescopeRestriction_isStableEquivalence f a

example (a : Under R) : IsStableEquivalence
    ((OpenTelescope.telescopeRestriction f).app a) :=
  OpenTelescope.telescopeRestriction_isStableEquivalence f a

end
