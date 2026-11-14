/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKStableComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedGroups

/-!
# Natural original supported K-group comparison on the actual coefficient pair row

The checked all-degree original evaluation equivalence assembles into a natural isomorphism
between the original supported K-pair functor and the actual fine section stable group functor.
This transports the original common-corner and chart maps, not degree-raising scalar operations.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedKStableNaturality.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The original supported K-pair functor naturally computes the same fine stable groups. -/
def boundedAboveFlatCoefficientSupportedKStableNatIso (n : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKFunctor n ≅
      boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor (n : ℤ) :=
  NatIso.ofComponents
    (fun a => (boundedAboveFlatCoefficientSupportedKStableEquiv f a n).toAddCommGrpIso) (by
      intro a b g
      ext x
      exact boundedAboveFlatCoefficientSupportedKStableEquiv_naturality f g n x.toMul)

end AlgebraicGeometry.Scheme.Modules
