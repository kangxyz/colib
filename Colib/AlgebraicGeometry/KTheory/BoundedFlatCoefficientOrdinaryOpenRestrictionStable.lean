/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeStableVanishing

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassTelescope
/-! # Stability of the original ordinary full-open Bass restriction

The actual graded target vanishing and stable cone comparison force the same restriction
cone to vanish; its actual cone-fiber equivalence gives all-signed restriction stability.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left]
/-- The same original restriction cone has no signed stable classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:259"
  "adaptation" "Original actual ordinary all-signed restriction stability"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)) d) := by
  let j := (stableHomotopyFunctor d).map
    ((boundedAboveFlatCoefficientOpenBassTelescopeConeComparison f).app a)
  have hi : Function.Injective j :=
    ((ConcreteCategory.isIso_iff_bijective j).mp
      (boundedAboveFlatCoefficientOpenBassTelescopeConeComparison_isStableEquivalence
        f a d)).injective
  exact ⟨fun x y ↦ hi
    ((boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d (j x)).trans
      (boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d (j y)).symm)⟩

/-- The actual original r-infinity is stable in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:272"
  "adaptation" "Original actual ordinary all-signed restriction stability"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) :=
  isStableEquivalence_of_cone_stableGroup_subsingleton _
    (boundedAboveFlatCoefficientOpenBassTelescopeRestriction_coneFiber_isStableEquivalence f a)
    (boundedAboveFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton f a)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0595"]
  boundedAboveFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence

attribute [colib_tag "COL-0595"]
  boundedAboveFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton

end AlgebraicGeometry.Scheme.Modules
