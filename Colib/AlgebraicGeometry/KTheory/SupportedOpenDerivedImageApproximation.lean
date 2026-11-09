/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.WeakArrowLift
public import Colib.KTheory.Waldhausen.WeakArrow.RelativeKEquivalence
public import Colib.KTheory.Waldhausen.Approximation.DualInverseImageLift
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps

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
namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
universe u d
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j T)]

/-- Coarse exactness retains the actual original relative source model. -/
theorem relativeCorestrict_isExact : IsExact
    (perfectSupportedOpenWeakWaldhausen j T).cof (perfectSupportedOpenWeakWaldhausen j T).weq
    (waldhausen j T Fact.out).cof (waldhausen j T Fact.out).weq (corestrict j T) where
  zero := (corestrict_isExact j T Fact.out).zero
  cofibration := (corestrict_isExact j T Fact.out).cofibration
  weak _ h := h
  pushout := (corestrict_isExact j T Fact.out).pushout


/-- Actual relative restriction is a K-equivalence onto the saturated image,
conditional only on the explicitly stated geometric roof property. -/
theorem relativeCorestrict_KMap_bijective
    (n : ℕ) :
    Function.Bijective (KMap (relativeCorestrict_isExact j T) n) := by
  let : (complexes U.Modules).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso U.Modules
      (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (waldhausen j T Fact.out).weq.HasTwoOutOfThreeProperty :=
    CofibrationClosedSubcategory.twoOutOfThree
      (complexes U.Modules) (complexObjects j T) (cofibrationClosed j T Fact.out)
  apply (WeakArrow.Relative.KMap_bijective_iff_target.{u+1,u}
    (perfectSupportedWaldhausen T.ι) (waldhausen j T Fact.out) (waldhausen j T Fact.out)
    (corestrict j T) (𝟭 _) (corestrict_isExact j T Fact.out)
    (IsExact.id (waldhausen j T Fact.out).cof (waldhausen j T Fact.out).weq) n).mpr
  exact KMap_bijective_of_dualLift_inverseImage
    (WeakArrow.dual_compatible (perfectSupportedWaldhausen T.ι) (waldhausen j T Fact.out)
      (perfectSupportedOppositeWaldhausen T.ι) (oppositeWaldhausen j T)
      (corestrict j T) (corestrict_isExact j T Fact.out) (corestrict_op_isExact j T)
      (oppositeWaldhausen_compatible j T)
      (perfectSupportedOppositeWaldhausen_compatible T.ι))
    (oppositeWaldhausen_compatible j T) (oppositeWaldhausen_compatible j T)
    (WeakArrow.target_exact (perfectSupportedWaldhausen T.ι) (waldhausen j T Fact.out)
      (corestrict j T) (corestrict_isExact j T Fact.out))
    (WeakArrow.dual_target_exact (perfectSupportedWaldhausen T.ι)
      (waldhausen j T Fact.out)
      (perfectSupportedOppositeWaldhausen T.ι) (oppositeWaldhausen j T)
      (corestrict j T) (corestrict_isExact j T Fact.out) (corestrict_op_isExact j T)
      (oppositeWaldhausen_compatible j T))
    (IsExact.id (waldhausen j T Fact.out).cof (waldhausen j T Fact.out).weq)
    (IsExact.id (oppositeWaldhausen j T).cof (oppositeWaldhausen j T).weq)
    (fun f => weakArrow_target_lift j T f) (weakArrowOppositeJointData j T) n

/-- The equivalence is induced by the original actual corestriction K-map. -/
def relativeCorestrictKEquiv (n : ℕ) :
    PerfectSupportedOpenCoarseK j T n ≃* (waldhausen j T Fact.out).K n :=
  MulEquiv.ofBijective (KMap (relativeCorestrict_isExact j T) n)
    (relativeCorestrict_KMap_bijective j T n)

@[simp] theorem relativeCorestrictKEquiv_apply (n : ℕ) (x : PerfectSupportedOpenCoarseK j T n) :
    relativeCorestrictKEquiv j T n x = KMap (relativeCorestrict_isExact j T) n x := rfl

/-- The actual inclusion after corestriction recovers the unchanged open K-map. -/
theorem relativeKMap_factor (n : ℕ) :
    (KMap (inclusion_isExact j T Fact.out) n).comp
      (relativeCorestrictKEquiv j T n).toMonoidHom = perfectSupportedOpenKRestrict j T n := by
  change (KMap (inclusion_isExact j T Fact.out) n).comp
    (KMap (relativeCorestrict_isExact j T) n) = _
  rw [KMap_comp_KMap]
  rfl

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
