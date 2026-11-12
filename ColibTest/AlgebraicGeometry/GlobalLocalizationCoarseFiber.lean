module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionCoarseFiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((SupportedTelescope.globalDiagram f i).obj a).space m) :
    ((null f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (SupportedTelescope.globalDiagram f k).obj a)
        (fun k ↦ (SupportedTelescope.globalTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (OpenTelescope.globalDiagram f k).obj a)
      (fun k ↦ (OpenTelescope.globalTransition f k).app a) m i
        (t, ((globalSupportedOpenFiniteNull f i).homotopy a).level m (s, x)) :=
  null_cylinder f a m i s t x

example (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((SupportedTelescope.globalTelescope f).obj a).space n) :
    ((OpenTelescope.telescopeRestriction f).app a).map n
      (((null f).homotopy a).level n (s, x)) =
    ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level n
      (s, ((SupportedTelescope.telescopeRestriction f).app a).map n x) :=
  null_restriction f a n s x

example (a : Under R) :
    fiberMap f a ≫ homotopyFiberMap (fiberSquare f a) =
      (SupportedTelescope.telescopeRestriction f).app a ≫
        homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a) :=
  fiberMap_restriction f a

example (a : Under R) : IsStableEquivalence (fiberMap f a) :=
  fiberMap_isStableEquivalence f a

end
