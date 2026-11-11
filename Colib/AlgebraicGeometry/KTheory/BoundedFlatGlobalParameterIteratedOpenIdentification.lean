/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullNull

/-! # The actual full-open map in the original selected-null telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Realization preserves the actual two-factor full-open Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterIteratedOpenIdentification.lean:25"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem parameterRestrictionMap_eq_fullMap :
    parameterRestrictionMap f = ParameterFullCurrentNull.fullMap f.left :=
  Functor.whiskerRight_comp _ _ _

/-- The original selected-null open map is the same entire quotient telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterIteratedOpenIdentification.lean:30"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem parameterTelescopeRestriction_eq_iteratedOpen :
    parameterTelescopeRestriction f = ParameterFullCurrentNull.iteratedOpen f.left := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram P)).obj X)
    (fun j => (strictDiagramTransition squareFunctor
      (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) j).app X)
        n i
      (t, (((strictDiagramIterate squareFunctor i).map
        (parameterRestrictionMap f)).app X).map n x) =
    Telescope.cylinder
      (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram P)).obj X)
      (fun j => (strictDiagramTransition squareFunctor
        (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) j).app
          X) n i
        (t, (((strictDiagramIterate squareFunctor i).map
          (ParameterFullCurrentNull.fullMap f.left)).app X).map n x)
  rw [parameterRestrictionMap_eq_fullMap]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
