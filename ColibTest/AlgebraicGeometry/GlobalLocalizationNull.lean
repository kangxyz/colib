module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationNull
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) (S : ((supportedRow f).obj a).obj.Obj) :
    (openModel f a).obj.waldhausen.weq ((globalZeroToOpen f a).app S) :=
  globalZeroToOpen_weak f a S

example (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((openRowRestriction f).app a)).map n
        (((globalSupportedOpenNull f).homotopy a).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n
        (s, (prespectrumMap ((supportedRowRestriction f).app a)).map n x) :=
  globalSupportedOpenNull_restriction f a n s x

end
