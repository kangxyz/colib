/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNaturalSeed
public import Colib.KTheory.Bass.StageAction
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquareFactor

/-! # The original whole scheme current-transition comparison

The actual original coefficient track, finite-stage seed and literal row target are retained.
No stable class substitutes for the whole map or normalized boundary homotopy.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack NormalizedStageMap
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The original action on each actual finite Bass stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean:29"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def stageTrack (A : Track laurent.op coefficient F) (i : ℕ) :
    Track laurent.op coefficient ((strictDiagramIterate squareFunctor i).obj F) :=
  A.stages (L := laurent.op) (c := coefficient) squareFunctor
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i

/-- Apply the original seed to the current stage and retain the original association cast. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean:43"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def currentTransition (A : Track laurent.op coefficient F) (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj F ⟶
      (strictDiagramIterate squareFunctor (i + 1)).obj F :=
  seed (stageTrack A i) ≫ eqToHom (bass_succ_eq squareFunctor i F).symm

end KTheory.Bass.SchemeNaturalSeed

attribute [colib_tag "COL-0555"]
  KTheory.Bass.SchemeNaturalSeed.currentTransition
