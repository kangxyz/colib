/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedInputNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull

/-! # The actual original seed-iterate full-open diagram and its selected null -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original iterated-seed supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIteratedFullNull.lean:24"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedForget := iteratedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The original iterated-seed full-open restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIteratedFullNull.lean:28"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedOpen := iteratedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The same selected full-open null on the original seed-iterate telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIteratedFullNull.lean:32"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedNull := iteratedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The original same-null full-open lift on the original seed-iterate model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIteratedFullNull.lean:37"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((iteratedOpen f).app X) ((iteratedForget f).app X)
    ((iteratedNull f).homotopy X)

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
