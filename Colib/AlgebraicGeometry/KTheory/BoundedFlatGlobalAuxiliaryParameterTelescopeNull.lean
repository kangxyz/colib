/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterFiniteNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNull
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFullOpenBassLocalization


/-! # The same original auxiliary G7 null on the complete integral Spec-row telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual three supported Spec-row comparisons retain every original G7 full-null value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeNull.lean:28"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem telescope_fullNull_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope
      (ParameterAuxiliarySupport.fiberAction f.left T)).obj (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (((ParameterAuxiliarySupport.iteratedNull f.left T).homotopy
        (specUnder.obj a)).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (s, ((fiberTelescopeComparison f T).app a).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
      (fun i => (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
      n z.1 (z.2.1, y)) (finite_fullNull_square f T z.1 a n s z.2.2)

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
