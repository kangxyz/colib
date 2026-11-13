/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassStages
public import Colib.Topology.Prespectrum.TelescopeDiagramMap


/-! # Literal auxiliary-supported coarse and fine-open telescope objects

The unchanged C/F finite diagrams and original seed transitions give their actual telescopes
and stage inclusions. The later coarse-to-fine restriction and graded contraction are separate.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original C completion, with its unchanged finite stages and original transitions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:42"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1}
  :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedOpenBassTransition f T)

/-- Original F completion of the actual auxiliary-supported native fine open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:47"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor : Under R ⥤
  LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T)

/-- Original C stage inclusions with the same initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:63"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedOpenBassTransition f T) i

/-- Original F stage inclusions with the same initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:70"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T) i

end AlgebraicGeometry.Scheme.Modules
