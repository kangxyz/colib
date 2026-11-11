/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedInduction
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedRotation

/-!
# The original iterated-seed tower and the fixed twisted-normalized tower

The unchanged finite stage map carries every original iterated-seed transition to
C0's actual twisted transition. The finite base input is supplied by the proved whole
geometric chi factorization, including the genuine two-cone permutation. There is no
additional tower-coherence or local geometric hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open NormalizedStageMap
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Every adjacent original iterated-seed square commutes with the unchanged stage map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedTransition.lean:33"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem originalTransition_stageMap (A : Track laurent.op coefficient F) (i : ℕ) :
    strictDiagramTransition squareFunctor (seed A) i ≫ stageMap squareFunctor (i + 1) F =
      stageMap squareFunctor i F ≫ twistedTransition A i := by
  apply originalTransition_stageMap_of_rotation A _ i
  intro j
  exact seed_cone_rotation (coneTrack A j)

end KTheory.Bass.SchemeIteratedSeedTransition
