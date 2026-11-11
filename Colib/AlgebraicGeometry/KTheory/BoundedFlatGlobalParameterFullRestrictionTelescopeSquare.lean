/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionSquare

/-! # The actual full-open Spec-row telescope square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The complete original full-open telescope factorization commutes with the Spec comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescopeSquare.lean:25"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullRestriction_telescope_square :
    Functor.whiskerLeft specUnder (parameterTelescopeRestriction f) ≫ (telescopeIso P).hom =
      (telescopeIso Q).hom ≫ LocalizationTelescope.openMap f ≫
        FullOpenTelescope.restriction f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder (fun j => (globalDiagram P j).obj a)
    (fun j => (globalTransition P j).app a) n i
    (t, ((finiteIso P i).hom.app a).map n
      (((parameterFiniteRestriction f i).app (specUnder.obj a)).map n x)) =
    Telescope.cylinder (fun j => (globalDiagram P j).obj a)
      (fun j => (globalTransition P j).app a) n i
      (t, ((FullOpenTelescope.finiteRestriction f i).app a).map n
        (((LocalizationTelescope.finiteOpen f i).app a).map n
          (((finiteIso Q i).hom.app a).map n x)))
  exact congrArg (fun y => Telescope.cylinder (fun j => (globalDiagram P j).obj a)
    (fun j => (globalTransition P j).app a) n i (t, y))
    (congrArg (fun η => (η.app a).map n x) (fullRestriction_finite_square f i))

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

