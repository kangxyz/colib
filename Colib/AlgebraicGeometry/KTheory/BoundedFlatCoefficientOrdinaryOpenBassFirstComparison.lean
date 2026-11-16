/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedOpenBassPositiveVanishing
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassTower
public import Colib.Topology.Prespectrum.ConeStableRangeDetection

/-!
# Positive-degree comparison of the ordinary open Bass rows

The genuine cone of the first restriction has no positive-degree stable groups;
therefore the actual first restriction is invertible in each such degree.

Source: `CoefficientOpenConnectiveInvertibility.lean` in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat`,
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
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The unchanged first coarse restriction is invertible in positive degrees. -/
theorem boundedAboveFlatCoefficientOpenBassRestriction_one_positive_isIso
    (a : Under R) (d : ℤ) (hd : 0 < d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenBassRestriction f 1).app a)) := by
  have hz (k : ℤ) (hk : 0 < k) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedAboveFlatCoefficientOpenBassRestriction f 1).app a)) k) := by
    let : Subsingleton ((stableHomotopyFunctor k).obj
        ((boundedAboveFlatCoefficientGradedOpenBassDiagram f 1).obj a)) :=
      boundedAboveFlatCoefficientGradedOpenBass_one_positive_subsingleton f a k hk
    let : IsIso ((stableHomotopyFunctor k).map
        ((boundedAboveFlatCoefficientOpenBassConeComparison f 1).app a)) :=
      boundedAboveFlatCoefficientOpenBassConeComparison_isStableEquivalence f 1 a k
    exact (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor k).map
        ((boundedAboveFlatCoefficientOpenBassConeComparison f 1).app a))).injective.subsingleton
  exact stableMap_isIso_of_cone_subsingleton _
    (boundedAboveFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence f 1 a)
    d (hz d hd) (hz (d + 1) (by omega))

end AlgebraicGeometry.Scheme.Modules
