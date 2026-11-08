/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Dense
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Flatten
public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageApproximation
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenKZeroImage
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

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]
  (hc : HasPerfectComplements j)

local notation "h" => denseCofiberData j Fact.out hc
local notation "W" => RingedSpace.perfectComplexesWaldhausen U.toRingedSpace

local instance : (flatten j).IsEquivalence := (flattenEquivalence j).isEquivalence_functor
local instance : (nest j).IsEquivalence := (flattenEquivalence j).isEquivalence_inverse

/-- Flattening is exact for the original inherited monomorphisms and quasi-isomorphisms. -/
theorem flatten_isExact :
    IsExact (h).waldhausenStructure.cof (h).waldhausenStructure.weq
      (waldhausen j Fact.out).cof (waldhausen j Fact.out).weq (flatten j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (nest j) _ hz
  cofibration _ hi := hi
  weak _ hf := hf
  pushout _ hp := hp.map (flatten j)

/-- The literal inverse is exact for the same actual map classes. -/
theorem nest_isExact :
    IsExact (waldhausen j Fact.out).cof (waldhausen j Fact.out).weq
      (h).waldhausenStructure.cof (h).waldhausenStructure.weq (nest j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (flatten j) _ hz
  cofibration _ hi := hi
  weak _ hf := hf
  pushout _ hp := hp.map (nest j)

/-- Exact flattening induces its actual original K-map equivalence. -/
def flattenKEquiv (n : ℕ) :
    (h).waldhausenStructure.K n ≃* (waldhausen j Fact.out).K n :=
  KEquivOfExactEquivalence (flattenEquivalence j) (flatten_isExact j hc) (nest_isExact j hc) n

/-- The forward comparison is literally the original flattening K-map. -/
@[simp] theorem flattenKEquiv_toMonoidHom (n : ℕ) :
    (flattenKEquiv j hc n).toMonoidHom = KMap (flatten_isExact j hc) n := rfl

/-- Exact flattening commutes with the original native inclusion map. -/
theorem flattenKEquiv_inclusion (n : ℕ) :
    (KMap (inclusion_isExact j Fact.out) n).comp (flattenKEquiv j hc n).toMonoidHom =
      KMap (h).inclusion_exact n := by
  rw [flattenKEquiv_toMonoidHom, KMap_comp_KMap]

/-- The inverse flattening comparison retains the same original inclusion homomorphism. -/
theorem flattenKEquiv_symm_inclusion (n : ℕ) :
    (KMap (h).inclusion_exact n).comp (flattenKEquiv j hc n).symm.toMonoidHom =
      KMap (inclusion_isExact j Fact.out) n := by
  ext x
  have hx := DFunLike.congr_fun (flattenKEquiv_inclusion j hc n)
    ((flattenKEquiv j hc n).symm x)
  exact hx.symm.trans (congrArg (KMap (inclusion_isExact j Fact.out) n)
    ((flattenKEquiv j hc n).apply_symm_apply x))

/-- Exact flattening preserves the actual inclusion range in every connective degree. -/
theorem flatten_inclusion_range (n : ℕ) :
    (KMap (inclusion_isExact j Fact.out) n).range = (KMap (h).inclusion_exact n).range := by
  have hr : (flattenKEquiv j hc n).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (flattenKEquiv j hc n).surjective
  rw [← flattenKEquiv_inclusion j hc n, MonoidHom.range_comp, hr, Subgroup.map_top]

/-- Actual native fine perfect joint data, with no geometric or cylinder hypothesis. -/
def targetFineJointData (U : Scheme.{u}) :
    RowFactorization.JointData (.refl (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)) :=
  RingedSpace.perfectComplexesJointData U.toRingedSpace (.refl _)

/-- Its original second endpoint is a genuine section. -/
theorem targetFineJointData_section (U : Scheme.{u}) :
    RowFactorization.SecondEndpointSection
      (.refl (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)) (targetFineJointData U) :=
  RingedSpace.perfectComplexesJointData_secondEndpointSection U.toRingedSpace (.refl _)

include hc in
/-- The actual honest-image inclusion is bijective in every positive degree. -/
theorem inclusion_KMap_succ_bijective (n : ℕ) :
    Function.Bijective (KMap (inclusion_isExact j Fact.out) (n + 1)) := by
  have hcomp := (h).inclusion_KMap_succ_bijective_general
    (targetFineJointData U) (targetFineJointData_section U) n
  rw [← flattenKEquiv_inclusion j hc (n + 1)] at hcomp
  exact ((flattenKEquiv j hc (n + 1)).bijective.of_comp_iff _).mp hcomp

include hc in
/-- The original honest-image inclusion is injective also in degree zero. -/
theorem inclusion_KMap_injective (n : ℕ) :
    Function.Injective (KMap (inclusion_isExact j Fact.out) n) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (flattenKEquiv j hc n).surjective x
  obtain ⟨b, rfl⟩ := (flattenKEquiv j hc n).surjective y
  apply congrArg (flattenKEquiv j hc n)
  apply (h).inclusion_KMap_injective_general
    (targetFineJointData U) (targetFineJointData_section U) n
  change ((KMap (inclusion_isExact j Fact.out) n).comp
    (flattenKEquiv j hc n).toMonoidHom) a =
      ((KMap (inclusion_isExact j Fact.out) n).comp
        (flattenKEquiv j hc n).toMonoidHom) b at hxy
  rwa [flattenKEquiv_inclusion] at hxy

/-- The positive equivalence retains the actual honest-image inclusion as forward map. -/
def inclusionKEquiv (n : ℕ) : (waldhausen j Fact.out).K (n + 1) ≃* (W).K (n + 1) :=
  MulEquiv.ofBijective (KMap (inclusion_isExact j Fact.out) (n + 1))
    (inclusion_KMap_succ_bijective j hc n)

@[simp] theorem inclusionKEquiv_apply (n : ℕ) (x : (waldhausen j Fact.out).K (n + 1)) :
    inclusionKEquiv j hc n x = KMap (inclusion_isExact j Fact.out) (n + 1) x := rfl

include hc in
/-- The original relative-open restriction map is bijective in every positive degree. -/
theorem relativeKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict j (n + 1)) := by
  rw [← relativeKMap_factor j (n + 1)]
  exact (inclusion_KMap_succ_bijective j hc n).comp
    (relativeCorestrict_KMap_bijective j (n + 1))

include hc in
/-- The original relative-open restriction is injective in every connective degree. -/
theorem relativeKRestrict_injective (n : ℕ) :
    Function.Injective (perfectOpenKRestrict j n) := by
  rw [← relativeKMap_factor j n]
  exact (inclusion_KMap_injective j hc n).comp
    (relativeCorestrict_KMap_bijective j n).injective

/-- The positive equivalence has the actual unchanged relative restriction as forward map. -/
def relativeKRestrictEquiv (n : ℕ) : PerfectOpenK j (n + 1) ≃* (W).K (n + 1) :=
  MulEquiv.ofBijective (perfectOpenKRestrict j (n + 1)) (relativeKRestrict_succ_bijective j hc n)

@[simp] theorem relativeKRestrictEquiv_apply (n : ℕ) (x : PerfectOpenK j (n + 1)) :
    relativeKRestrictEquiv j hc n x = perfectOpenKRestrict j (n + 1) x := rfl

/-- Degree zero identifies exactly the actual fine global restriction-image subgroup. -/
def relativeKZeroImageEquiv : PerfectOpenK j 0 ≃* PerfectOpenKZeroImage j :=
  MulEquiv.ofBijective (perfectOpenKZeroToImage j)
    ⟨fun _ _ hxy => relativeKRestrict_injective j hc 0 (congrArg Subtype.val hxy),
      perfectOpenKZeroToImage_surjective j⟩

/-- Forgetting image membership recovers the literal original degree-zero endpoint. -/
@[simp] theorem relativeKZeroImageEquiv_coe (x : PerfectOpenK j 0) :
    (relativeKZeroImageEquiv j hc x : (W).K 0) = perfectOpenKRestrict j 0 x := rfl

/-- The honest-image inclusion has exactly the original fine restriction range in degree zero. -/
theorem range_inclusion_KMap_zero :
    (KMap (inclusion_isExact j Fact.out) 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range := by
  have hr : (relativeCorestrictKEquiv j 0).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (relativeCorestrictKEquiv j 0).surjective
  rw [← range_perfectOpenKRestrict_zero j, ← relativeKMap_factor j 0,
    MonoidHom.range_comp, hr, Subgroup.map_top]

/-- The constructed dense inclusion has exactly the original fine restriction range at zero. -/
theorem range_dense_inclusion_KMap_zero :
    (KMap (h).inclusion_exact 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range := by
  rw [← flatten_inclusion_range j hc 0, range_inclusion_KMap_zero j]

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Flatten.lean:51-106"
    "adaptation"
    "Exact native flattening and actual inclusion cofinality with constructed density \
    and fine joint data"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.flattenKEquiv
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.flattenKEquiv_inclusion
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.inclusion_KMap_succ_bijective
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.inclusion_KMap_injective

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KTheory.lean:36-83"
    "adaptation"
    "Original relative restriction endpoints; only actual native roofs \
    and complex-complement existence remain"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKRestrict_succ_bijective
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKRestrict_injective
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKRestrictEquiv
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKZeroImageEquiv
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.relativeKZeroImageEquiv_coe

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Flatten.lean:108-123"
    "adaptation" "Inverse and all-degree range comparison retain \
    the original actual inclusion maps"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.flattenKEquiv_symm_inclusion
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.flatten_inclusion_range

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KZeroCover.lean:29-41"
    "adaptation"
    "Actual inclusion range equals fine restriction range; geometric inputs remain explicit, \
    no cover reflection"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.range_inclusion_KMap_zero
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.range_dense_inclusion_KMap_zero
