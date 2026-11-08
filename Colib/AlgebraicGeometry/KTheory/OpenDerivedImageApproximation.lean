/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.WeakArrowLift
public import Colib.KTheory.Waldhausen.WeakArrow.RelativeKEquivalence
public import Colib.KTheory.Waldhausen.Approximation.DualInverseImageLift
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport

/-! # Relative restriction is a K-equivalence onto its honest derived image

The genuine incoming lifts and the constructed opposite weak-arrow joint data
supply every categorical input of dual inverse-image approximation. Only the precise
geometric global-perfect-model roof property remains an input. The actual canonical
K-map is bijective in every connective degree, including degree zero. This theorem
does not assert qcqs localization or surjectivity onto all perfect K-zero of the open.

Adapted from Quillen `AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Approximation.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, discharging its joint-data input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
universe u d
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]

/-- Actual relative restriction is a K-equivalence onto the saturated image,
conditional only on the explicitly stated geometric roof property. -/
theorem relativeCorestrict_KMap_bijective
    (n : ℕ) :
    Function.Bijective (KMap (relativeCorestrict_isExact j) n) := by
  let : (complexes U.Modules).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso U.Modules
      (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (waldhausen j Fact.out).weq.HasTwoOutOfThreeProperty :=
    CofibrationClosedSubcategory.twoOutOfThree
      (complexes U.Modules) (complexObjects j) (cofibrationClosed j Fact.out)
  apply (WeakArrow.Relative.KMap_bijective_iff_target.{u+1,u}
    (perfectComplexesWaldhausen X.toRingedSpace) (waldhausen j Fact.out) (waldhausen j Fact.out)
    (corestrict j) (𝟭 _) (corestrict_isExact j Fact.out)
    (IsExact.id (waldhausen j Fact.out).cof (waldhausen j Fact.out).weq) n).mpr
  exact KMap_bijective_of_dualLift_inverseImage
    (WeakArrow.dual_compatible (perfectComplexesWaldhausen X.toRingedSpace) (waldhausen j Fact.out)
      (perfectComplexesOppositeWaldhausen X.toRingedSpace) (oppositeWaldhausen j)
      (corestrict j) (corestrict_isExact j Fact.out) (corestrict_op_isExact j)
      (oppositeWaldhausen_compatible j)
      (perfectComplexesOppositeWaldhausen_compatible X.toRingedSpace))
    (oppositeWaldhausen_compatible j) (oppositeWaldhausen_compatible j)
    (WeakArrow.target_exact (perfectComplexesWaldhausen X.toRingedSpace) (waldhausen j Fact.out)
      (corestrict j) (corestrict_isExact j Fact.out))
    (WeakArrow.dual_target_exact (perfectComplexesWaldhausen X.toRingedSpace)
      (waldhausen j Fact.out)
      (perfectComplexesOppositeWaldhausen X.toRingedSpace) (oppositeWaldhausen j)
      (corestrict j) (corestrict_isExact j Fact.out) (corestrict_op_isExact j)
      (oppositeWaldhausen_compatible j))
    (IsExact.id (waldhausen j Fact.out).cof (waldhausen j Fact.out).weq)
    (IsExact.id (oppositeWaldhausen j).cof (oppositeWaldhausen j).weq)
    (fun f => weakArrow_target_lift j f) (weakArrowOppositeJointData j) n

/-- The equivalence is induced by the original actual corestriction K-map. -/
def relativeCorestrictKEquiv (n : ℕ) :
    PerfectOpenK j n ≃* (waldhausen j Fact.out).K n :=
  MulEquiv.ofBijective (KMap (relativeCorestrict_isExact j) n)
    (relativeCorestrict_KMap_bijective j n)

@[simp] theorem relativeCorestrictKEquiv_apply (n : ℕ) (x : PerfectOpenK j n) :
    relativeCorestrictKEquiv j n x = KMap (relativeCorestrict_isExact j) n x := rfl

/-- The actual inclusion after corestriction recovers the unchanged open K-map. -/
theorem relativeKMap_factor (n : ℕ) :
    (KMap (inclusion_isExact j Fact.out) n).comp
      (relativeCorestrictKEquiv j n).toMonoidHom = perfectOpenKRestrict j n := by
  change (KMap (inclusion_isExact j Fact.out) n).comp
    (KMap (relativeCorestrict_isExact j) n) = _
  rw [KMap_comp_KMap]
  rfl

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0314",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Approximation.lean:95-119"
    "adaptation"
    "Actual corestriction KMap bijectivity; genuine joint data is constructed, \
    roofs remain explicit"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeCorestrict_KMap_bijective
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeCorestrictKEquiv

attribute [colib_tag "COL-0314",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KTheory.lean:30-34"
    "adaptation" "Literal factorization of the existing relative-open restriction K-map"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKMap_factor
