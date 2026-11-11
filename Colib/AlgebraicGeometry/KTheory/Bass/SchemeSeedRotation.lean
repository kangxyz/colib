/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedRotationPointwise

/-!
# The actual finite Scheme seed rotation

The accepted whole geometric chi factorization, the original seed cospan, and the
fixed Bass-strength factorization imply the local base equation. The original inverse
loop transpose and the genuine two-cone geometric permutation remain explicit.
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
open FiniteConeTopology IteratedLoopStrength FiniteLoopWords
open GeometricConeInterchange LoopFactor
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The genuine two-cone permutation gives the exact finite rotation of the original seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedRotation.lean:32"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem seed_cone_rotation (A : Track laurent.op coefficient F) :
    (strictDiagramFunctor squareFunctor).map (seed A) ≫
        strengthDiagram squareFunctor (iterate squareFunctor 1 F) =
      Functor.whiskerRight (seed (coneTrack A 1)) parameterLoopingFunctor ≫
        (transposeIso (iterate squareFunctor 2 F)).inv ≫
        loopMap 2 (permutationNatIso F).hom := by
  apply NatTrans.ext
  funext X
  exact eq_of_heq (seed_cone_rotation_app_heq A X)

end KTheory.Bass.SchemeIteratedSeedTransition

namespace KTheory.Bass.SchemeIteratedSeedTransition

attribute [colib_tag "COL-0583"] seed_cone_rotation

end KTheory.Bass.SchemeIteratedSeedTransition
