/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassSeed
public import Colib.KTheory.Bass.StrictDiagram


/-! # Literal auxiliary-supported coarse and fine-open Bass stages

Only the original C/F stage and transition definitions needed by the actual auxiliary
fiber tower are selected. The same original seeds are iterated, without assuming a later
localization or graded contraction. No graded G row is introduced by this owner.
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

/-- Original finite C_Z stages of the auxiliary-supported coarse coefficient Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:38"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T)

/-- Original finite F stages of the same native fine open Model row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:43"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFullOpenBassDiagram (i : ℕ) : Under R ⥤
  LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T)

/-- Every actual C transition is the original iterated coarse seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:48"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenBassSeed
    f T) i

/-- Every actual F transition is the original iterated fine seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:55"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFullOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T) i

end AlgebraicGeometry.Scheme.Modules
