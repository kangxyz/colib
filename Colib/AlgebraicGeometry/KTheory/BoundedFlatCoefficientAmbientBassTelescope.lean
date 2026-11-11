/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassSeed
public import Colib.Topology.Prespectrum.TelescopeDiagramMap

/-! # The original fine ambient Bass stages and quotient telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- Literal finite Bass iterates of the original native fine ambient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassTower.lean:39"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientBassDiagram (Q : Over (Spec R)) (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q)

/-- The unchanged finite ambient transition is the original iterated ambient seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassTower.lean:52"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientBassTransition (Q : Over (Spec R)) (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedAboveFlatCoefficientAmbientBassDiagram Q (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientAmbientBassSeed Q) i

/-- Original native fine ambient completion with its unchanged finite stages and seeds. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassTelescope.lean:40"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientBassTelescopeFunctor (Q : Over (Spec R)) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientAmbientBassDiagram Q)
    (boundedAboveFlatCoefficientAmbientBassTransition Q)

/-- The original ambient finite-stage inclusions into its completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassTelescope.lean:71"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def boundedAboveFlatCoefficientAmbientBassTelescopeInclusion (Q : Over (Spec R)) (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientAmbientBassDiagram Q)
    (boundedAboveFlatCoefficientAmbientBassTransition Q) i

end AlgebraicGeometry.Scheme.Modules
