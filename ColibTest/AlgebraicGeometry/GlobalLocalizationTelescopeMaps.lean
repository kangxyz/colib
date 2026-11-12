module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeSquares
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

example (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((SupportedTelescope.globalDiagram f i).obj a).space n) :
    ((forget f).app a).map n
      (Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i (t, x)) =
    Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
      (fun j => (globalTransition Q j).app a) n i
      (t, ((finiteForget f i).app a).map n x) :=
  forget_cylinder f a n i t x

example (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((globalDiagram Q i).obj a).space n) :
    ((openMap f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
        (fun j => (globalTransition Q j).app a) n i (t, x)) =
    Telescope.cylinder (fun j => (OpenTelescope.globalDiagram f j).obj a)
      (fun j => (OpenTelescope.globalTransition f j).app a) n i
      (t, ((finiteOpen f i).app a).map n x) :=
  openMap_cylinder f a n i t x

example :
    SupportedTelescope.telescopeRestriction f ≫
      boundedAboveFlatCoefficientSupportedBassTelescopeForget f =
      forget f ≫ telescopeRestriction Q :=
  forget_square f

example :
    openMap f ≫ OpenTelescope.telescopeRestriction f =
      telescopeRestriction Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeOpen f :=
  open_square f

end
