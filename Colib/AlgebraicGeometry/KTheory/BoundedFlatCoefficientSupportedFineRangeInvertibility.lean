/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedConnectiveInvertibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBottomChartExactness
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedRangeFromAmbient

/-!
# The original fine supported Bass transitions are invertible in their full finite-stage range

For a qcqs ambient scheme and compact removed open, the actual stage-i transition is an
isomorphism on every stable group in degree at least minus i. The proof uses the actual
inter-stage short-exact row map,
the original connective seed, and the proved original bottom chart exactness. At the new
bottom degree its right terms vanish; above it, the previous-stage isomorphisms act at all
four original coefficient vertices. No all-stage comparison with the raw tower is assumed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedFineRangeInvertibility.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Topology Topology.LoopPrespectrum KTheory.Bass KTheory.Bass.TwoChartStable
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Every actual supported transition is invertible throughout its genuine finite-stage range. -/
theorem boundedAboveFlatCoefficientSupportedBassTransition_isIso_of_le (i : ℕ)
    (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f i).app a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact boundedAboveFlatCoefficientSupportedBassTransition_isIso_of_le_of_two_ambient f
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso P a n)
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso Q a n)
    (fun a i => boundedAboveFlatCoefficientSupportedBottomBassRight_isZero f a i) i a d hd

end AlgebraicGeometry.Scheme.Modules
