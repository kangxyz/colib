/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingSquare

/-! # The actual polynomial projection specialization of whole evaluation coherence -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputProjectionSquare

export InputCommutingSquare (firstLeg totalLeg compositionLegs)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The genuine projection naturality transports only the common source. -/
theorem source_eq :
    sectionMap (polynomial.map g ≫ projection.app Y) ≫ evaluation (polynomial.obj X) =
      sectionMap (projection.app X ≫ g) ≫ evaluation (polynomial.obj X) :=
  InputCommutingSquare.source_eq
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- Strict precomposition of the unchanged original X evaluation track. -/
def sourceTrack := InputCommutingSquare.sourceTrack
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- The second original total composition in the projection square. -/
def secondTotal := InputCommutingSquare.secondTotal
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- The whole original second composition comparison at the common source. -/
def secondComparison := InputCommutingSquare.secondComparison
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- The evaluated original raw polynomial square, with its unchanged split clock. -/
def rawTrack := InputCommutingSquare.rawTrack
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- Y evaluation followed by the complete original raw projection square. -/
def targetTrack := InputCommutingSquare.targetTrack
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

/-- All four original evaluation/projection legs bound a genuine whole square. -/
def square := InputCommutingSquare.square
  (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputProjectionSquare
