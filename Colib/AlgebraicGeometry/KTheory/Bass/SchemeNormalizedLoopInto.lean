/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTransitions
public import Colib.KTheory.Bass.FiniteLoopConjugacy

/-! # The literal normalized seed as the fixed casted finite-loop map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open FiniteLoopWordSlide
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Both constructions retain the identical complete functor association equality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeNormalizedLoopInto.lean:27"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
theorem normalizedTransition_loopInto (A : Track laurent.op coefficient F) (i : ℕ) :
    normalizedTransition A i = loopInto i (seed (coneTrack A i)) :=
  (loopInto_eq i
    (A := FiniteConeTopology.iterate squareFunctor i F)
    (B := FiniteConeTopology.iterate squareFunctor (i + 1) F)
    (seed (coneTrack A i))).symm

end KTheory.Bass.SchemeNaturalSeed
