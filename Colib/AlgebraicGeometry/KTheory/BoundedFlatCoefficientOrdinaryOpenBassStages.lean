/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
public import Colib.KTheory.Bass.StrictDiagram
public import Colib.Topology.Prespectrum.TelescopeDiagram
/-! # Original ordinary coarse and fine open stages and completions

These eight declarations retain the original C/F stages, seed transitions and inclusions.
Restriction maps and their stability are separate subsequent results.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
/-- Original finite C stages of the actual coarse native coefficient Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTower.lean:39"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientOpenPrespectrumFunctor f)

/-- Original finite F stages of the same native fine open Model row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTower.lean:44"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientFullOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f)

/-- Every actual C transition is the original iterated coarse seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTower.lean:49"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassDiagram f i ⟶ boundedAboveFlatCoefficientOpenBassDiagram f
      (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (boundedAboveFlatCoefficientOpenBassSeed
    f) i

/-- Every actual F transition is the original iterated fine seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTower.lean:54"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientFullOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientFullOpenBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientFullOpenBassSeed f) i

/-- Original C completion, with its unchanged finite stages and original transitions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTelescope.lean:42"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientOpenBassDiagram f)
    (boundedAboveFlatCoefficientOpenBassTransition f)

/-- Original F completion of the actual native fine open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTelescope.lean:47"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientFullOpenBassDiagram f)
    (boundedAboveFlatCoefficientFullOpenBassTransition f)

/-- Original C stage inclusions with the same initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTelescope.lean:61"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientOpenBassDiagram f)
    (boundedAboveFlatCoefficientOpenBassTransition f) i

/-- Original F stage inclusions with the same initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientOpenBassTelescope.lean:67"
  "adaptation" "Original ordinary C/F finite stages and telescope inclusions"]
def boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientFullOpenBassDiagram f)
    (boundedAboveFlatCoefficientFullOpenBassTransition f) i
end AlgebraicGeometry.Scheme.Modules
