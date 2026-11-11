module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenTelescope
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism
universe u
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.OpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram f i).obj a).space n) :
    ((telescopeRestriction f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram f j).obj a)
        (fun j => (globalTransition f j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedAboveFlatCoefficientOpenBassDiagram f j).obj a)
      (fun j => (boundedAboveFlatCoefficientOpenBassTransition f j).app a) n i
      (s, ((finiteRestriction f i).app a).map n x) :=
  telescopeRestriction_cylinder f a n i s x

example (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i ≫
      telescopeRestriction f =
    finiteRestriction f i ≫ boundedAboveFlatCoefficientOpenBassTelescopeInclusion f i :=
  telescopeRestriction_inclusion f i

end
