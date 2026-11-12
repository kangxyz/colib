/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTelescope

/-! # Exact stage and height formulas for the actual supported parameter comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual row isomorphism retains every stage and the independent telescope height. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeCells.lean:26"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescopeIso_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval)
    (x : ((strictDiagramIterate squareFunctor i).obj (parameterDiagram f)).obj
      (specUnder.obj a) |>.space n) :
    ((telescopeIso f).hom.app a).map n
      (Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram f)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) j).app
          (specUnder.obj a)) n i (t, x)) =
      Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i
        (t, ((finiteIso f i).hom.app a).map n x) := rfl

/-- The inverse isomorphism preserves the same original quotient coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeCells.lean:42"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescopeIso_inv_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval) (x : ((SupportedTelescope.globalDiagram f i).obj a).space n) :
    ((telescopeIso f).inv.app a).map n
      (Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram f)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) j).app
          (specUnder.obj a)) n i (t, ((finiteIso f i).inv.app a).map n x) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient

