/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialComparison

/-! Stability of the whole natural comparison, with original source-track transport. -/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialComparisonStable.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan

/-- Every component of the original-source natural comparison is a stable equivalence. -/
theorem comparisonNatTransOfEq_stable
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((comparisonNatTransOfEq M A B h).app X) := by
  rw [comparisonNatTransOfEq_app]
  exact comparisonOfEq_stable M A B h X

end KTheory.Bass.SchemeTrackSequentialPresentation
