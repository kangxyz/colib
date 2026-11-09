/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Dense
public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Flatten
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenDerivedImageApproximation
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenKZeroImage
public import Colib.KTheory.Waldhausen.Cofinality.GeneralDense

/-!
# Native honest-image cofinality and the actual fine restriction endpoints

Actual native perfect roofs and actual complex-complement existence construct dense cofiber
data. The original native fine cylinder and its actual second endpoint section discharge
all categorical cofinality inputs. The honest image inclusion and the unchanged relative
restriction are injective in every connective degree and bijective in positive degrees.
In degree zero the canonical equivalence has exactly the actual fine restriction image as
codomain, and forgetting image membership recovers the original map literally.

The two geometric inputs remain explicit. No qcqs roof or complement existence, outgoing
App2, surjectivity onto all target K-zero, or final qcqs localization is asserted here.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Flatten.lean`
and `KTheory.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j T)]
  (hc : HasPerfectComplements j T)

local notation "h" => denseCofiberData j T Fact.out hc
set_option quotPrecheck false in
local notation "W" => perfectSupportedWaldhausen (Scheme.Opens.ι (j ⁻¹ᵁ T))

local instance : (flatten j T).IsEquivalence := (flattenEquivalence j T).isEquivalence_functor
local instance : (nest j T).IsEquivalence := (flattenEquivalence j T).isEquivalence_inverse

/-- Flattening is exact for the original inherited monomorphisms and quasi-isomorphisms. -/
theorem flatten_isExact :
    IsExact (h).waldhausenStructure.cof (h).waldhausenStructure.weq
      (waldhausen j T Fact.out).cof (waldhausen j T Fact.out).weq (flatten j T) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (nest j T) _ hz
  cofibration _ hi := hi
  weak _ hf := hf
  pushout _ hp := hp.map (flatten j T)

/-- The literal inverse is exact for the same actual map classes. -/
theorem nest_isExact :
    IsExact (waldhausen j T Fact.out).cof (waldhausen j T Fact.out).weq
      (h).waldhausenStructure.cof (h).waldhausenStructure.weq (nest j T) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (flatten j T) _ hz
  cofibration _ hi := hi
  weak _ hf := hf
  pushout _ hp := hp.map (nest j T)

/-- Exact flattening induces its actual original K-map equivalence. -/
def flattenKEquiv (n : ℕ) :
    (h).waldhausenStructure.K n ≃* (waldhausen j T Fact.out).K n :=
  KEquivOfExactEquivalence (flattenEquivalence j T) (flatten_isExact j T hc) (nest_isExact j T hc) n

/-- The forward comparison is literally the original flattening K-map. -/
@[simp] theorem coe_flattenKEquiv (n : ℕ) :
    (flattenKEquiv j T hc n : (h).waldhausenStructure.K n →* (waldhausen j T Fact.out).K n) =
      KMap (flatten_isExact j T hc) n := rfl

/-- Exact flattening commutes with the original native inclusion map. -/
theorem flattenKEquiv_inclusion (n : ℕ) :
    (KMap (inclusion_isExact j T Fact.out) n).comp (flattenKEquiv j T hc n).toMonoidHom =
      KMap (h).inclusion_exact n := by
  rw [MulEquiv.toMonoidHom_eq_coe, coe_flattenKEquiv, KMap_comp_KMap]

/-- The inverse flattening comparison retains the same original inclusion homomorphism. -/
theorem flattenKEquiv_symm_inclusion (n : ℕ) :
    (KMap (h).inclusion_exact n).comp (flattenKEquiv j T hc n).symm.toMonoidHom =
      KMap (inclusion_isExact j T Fact.out) n := by
  ext x
  have hx := DFunLike.congr_fun (flattenKEquiv_inclusion j T hc n)
    ((flattenKEquiv j T hc n).symm x)
  exact hx.symm.trans (congrArg (KMap (inclusion_isExact j T Fact.out) n)
    ((flattenKEquiv j T hc n).apply_symm_apply x))

/-- Exact flattening preserves the actual inclusion range in every connective degree. -/
theorem flatten_inclusion_range (n : ℕ) :
    (KMap (inclusion_isExact j T Fact.out) n).range = (KMap (h).inclusion_exact n).range := by
  have hr : (flattenKEquiv j T hc n).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (flattenKEquiv j T hc n).surjective
  rw [← flattenKEquiv_inclusion j T hc n, MonoidHom.range_comp, hr, Subgroup.map_top]

/-- The supported fine target has its actual native cylinder. -/
def targetFineJointData : RowFactorization.JointData
    (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)) :=
  perfectSupportedJointData (j ⁻¹ᵁ T).ι (.refl _)

omit [IsOpenImmersion j] [HasDerivedCategory U.Modules] [Fact (HasDerivedRoofs j T)] in
/-- The actual second endpoint is a genuine section. -/
theorem targetFineJointData_section : RowFactorization.SecondEndpointSection
    (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)) (targetFineJointData j T) :=
  perfectSupportedJointData_secondEndpointSection (j ⁻¹ᵁ T).ι (.refl _)

include hc in
/-- The actual honest-image inclusion is bijective in every positive degree. -/
theorem inclusion_KMap_succ_bijective (n : ℕ) :
    Function.Bijective (KMap (inclusion_isExact j T Fact.out) (n + 1)) := by
  have hcomp := (h).inclusion_KMap_succ_bijective_general
    (targetFineJointData j T) (targetFineJointData_section j T) n
  rw [← flattenKEquiv_inclusion j T hc (n + 1)] at hcomp
  exact ((flattenKEquiv j T hc (n + 1)).bijective.of_comp_iff _).mp hcomp

include hc in
/-- The original honest-image inclusion is injective also in degree zero. -/
theorem inclusion_KMap_injective (n : ℕ) :
    Function.Injective (KMap (inclusion_isExact j T Fact.out) n) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (flattenKEquiv j T hc n).surjective x
  obtain ⟨b, rfl⟩ := (flattenKEquiv j T hc n).surjective y
  apply congrArg (flattenKEquiv j T hc n)
  apply (h).inclusion_KMap_injective_general
    (targetFineJointData j T) (targetFineJointData_section j T) n
  change ((KMap (inclusion_isExact j T Fact.out) n).comp
    (flattenKEquiv j T hc n).toMonoidHom) a =
      ((KMap (inclusion_isExact j T Fact.out) n).comp
        (flattenKEquiv j T hc n).toMonoidHom) b at hxy
  rwa [flattenKEquiv_inclusion] at hxy

/-- The positive equivalence retains the actual honest-image inclusion as forward map. -/
def inclusionKEquiv (n : ℕ) : (waldhausen j T Fact.out).K (n + 1) ≃* (W).K (n + 1) :=
  MulEquiv.ofBijective (KMap (inclusion_isExact j T Fact.out) (n + 1))
    (inclusion_KMap_succ_bijective j T hc n)

@[simp] theorem inclusionKEquiv_apply (n : ℕ) (x : (waldhausen j T Fact.out).K (n + 1)) :
    inclusionKEquiv j T hc n x = KMap (inclusion_isExact j T Fact.out) (n + 1) x := rfl

include hc in
/-- The original relative-open restriction map is bijective in every positive degree. -/
theorem relativeKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n + 1)) := by
  rw [← relativeKMap_factor j T (n + 1)]
  exact (inclusion_KMap_succ_bijective j T hc n).comp
    (relativeCorestrict_KMap_bijective j T (n + 1))

include hc in
/-- The original relative-open restriction is injective in every connective degree. -/
theorem relativeKRestrict_injective (n : ℕ) :
    Function.Injective (perfectSupportedOpenKRestrict j T n) := by
  rw [← relativeKMap_factor j T n]
  exact (inclusion_KMap_injective j T hc n).comp
    (relativeCorestrict_KMap_bijective j T n).injective

/-- The positive equivalence has the actual unchanged relative restriction as forward map. -/
def relativeKRestrictEquiv (n : ℕ) : PerfectSupportedOpenCoarseK j T (n + 1) ≃* (W).K (n + 1) :=
  MulEquiv.ofBijective (perfectSupportedOpenKRestrict j T (n + 1))
    (relativeKRestrict_succ_bijective j T hc n)

@[simp] theorem relativeKRestrictEquiv_apply (n : ℕ) (x : PerfectSupportedOpenCoarseK j T (n + 1)) :
    relativeKRestrictEquiv j T hc n x = perfectSupportedOpenKRestrict j T (n + 1) x := rfl

/-- Degree zero identifies exactly the actual fine global restriction-image subgroup. -/
def relativeKZeroImageEquiv :
    PerfectSupportedOpenCoarseK j T 0 ≃* PerfectSupportedOpenKZeroImage j T :=
  MulEquiv.ofBijective (perfectSupportedOpenKZeroToImage j T)
    ⟨fun _ _ hxy => relativeKRestrict_injective j T hc 0 (congrArg Subtype.val hxy),
      perfectSupportedOpenKZeroToImage_surjective j T⟩

/-- Forgetting image membership recovers the literal original degree-zero endpoint. -/
@[simp] theorem relativeKZeroImageEquiv_coe (x : PerfectSupportedOpenCoarseK j T 0) :
    (relativeKZeroImageEquiv j T hc x : (W).K 0) = perfectSupportedOpenKRestrict j T 0 x := rfl

/-- The honest-image inclusion has exactly the original fine restriction range in degree zero. -/
theorem range_inclusion_KMap_zero :
    (KMap (inclusion_isExact j T Fact.out) 0).range =
      (KMap (perfectSupportedRestrict_exact j T) 0).range := by
  have hr : (relativeCorestrictKEquiv j T 0).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (relativeCorestrictKEquiv j T 0).surjective
  change (KMap (inclusion_isExact j T Fact.out) 0).range =
    (perfectSupportedKRestrict j T 0).range
  rw [← range_perfectSupportedOpenKRestrict_zero j T, ← relativeKMap_factor j T 0,
    MonoidHom.range_comp, hr, Subgroup.map_top]

/-- The constructed dense inclusion has exactly the original fine restriction range at zero. -/
theorem range_dense_inclusion_KMap_zero :
    (KMap (h).inclusion_exact 0).range =
      (KMap (perfectSupportedRestrict_exact j T) 0).range := by
  rw [← flatten_inclusion_range j T hc 0, range_inclusion_KMap_zero j T]

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
