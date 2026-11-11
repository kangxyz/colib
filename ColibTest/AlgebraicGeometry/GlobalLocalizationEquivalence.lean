module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationEquivalence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a) :=
  supportedRowRestriction_iterate_isStableEquivalence f S i a

example
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a) :=
  openRowRestriction_iterate_isStableEquivalence f S i a

end
