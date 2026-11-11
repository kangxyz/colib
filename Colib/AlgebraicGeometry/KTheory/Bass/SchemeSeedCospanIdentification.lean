/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageSquare
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan

/-! # Exact identification of the existing Scheme seed in the finite geometric cospan -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open IteratedLoopStrength GeometricSquareInterchange
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The original all-scheme seed retains exactly the original source-track endpoint casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedCospanIdentification.lean:26"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem seed_sourceTrack (A : Track laurent.op coefficient F) :
    SchemeNaturalSeed.seed A =
      WholeSeedCospan.seed (geometricSquare F) (sourceTrack F A.homotopy)
        (sourceTrack_naturality F A.homotopy A.naturality) := rfl

/-- The original Bass action has exactly the endpoint casts used by the geometric cospan. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedCospanIdentification.lean:32"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem sourceTrack_bassTrack (A : Track laurent.op coefficient F) :
    sourceTrack ((strictDiagramFunctor squareFunctor).obj F)
      (stageTrack A 1).homotopy =
      bassTrack F A.homotopy A.naturality := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
