/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialPresentation
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope

/-! Transport the genuine presentation comparison along an equality of entire original tracks. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ)

/-- Keep the source telescope literal while transporting the whole chosen presentation track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialTransport.lean:25"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def comparisonOfEq : (SchemeNaturalSeed.currentTelescope A).obj X ⟶ presentation M B X := by
  subst B
  exact comparison M A X

/-- Equality transport of entire tracks preserves the actual stable comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialTransport.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparisonOfEq_stable : IsStableEquivalence (comparisonOfEq M A B h X) := by
  subst B
  exact comparison_stable M A X

end KTheory.Bass.SchemeTrackSequentialPresentation
