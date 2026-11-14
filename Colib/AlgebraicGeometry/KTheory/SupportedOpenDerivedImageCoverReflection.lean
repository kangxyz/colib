/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.CoverReflection
public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.QcqsGeometry
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenDerivedImageCofinality
public import Colib.KTheory.Waldhausen.Cofinality.ImageReflection
public import Colib.AlgebraicGeometry.KTheory.SupportedRestrictionComparison

/-! # Reflection of the supported K-zero image across two opens -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "W" => Scheme.Opens.toScheme I₀
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀
local notation "a" => Scheme.Hom.resLE j T I₀ le_rfl

local instance supportedKZeroOverlapOpen : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The literal overlap functor restricts the original complexes, identifying
only the equality of the two inverse-image opens. -/
def overlapRestrict :
    (perfectSupported (i ⁻¹ᵁ Z).ι).FullSubcategory ⥤
      (perfectSupported (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).FullSubcategory :=
  perfectSupportedRestrictCongr a (i ⁻¹ᵁ Z) (coverAuxiliaryPreimage_eq j T Z)

/-- The actual overlap restriction remains Waldhausen exact. -/
theorem overlapRestrict_exact :
    IsExact (perfectSupportedWaldhausen (i ⁻¹ᵁ Z).ι).cof
      (perfectSupportedWaldhausen (i ⁻¹ᵁ Z).ι).weq
      (perfectSupportedWaldhausen (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).cof
      (perfectSupportedWaldhausen (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).weq
      (overlapRestrict j T Z) := by
  unfold overlapRestrict perfectSupportedRestrictCongr
  generalize coverAuxiliaryPreimage_eq j T Z = h
  revert h
  generalize (b ⁻¹ᵁ (j ⁻¹ᵁ Z)) = A
  intro h
  subst A
  exact perfectSupportedRestrict_exact a (i ⁻¹ᵁ Z)

/-- The overlap restriction keeps each original cochain complex. -/
theorem overlapRestrict_obj (K : (perfectSupported (i ⁻¹ᵁ Z).ι).FullSubcategory) :
    ((overlapRestrict j T Z).obj K).obj =
      (((restrictFunctor a).mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  unfold overlapRestrict perfectSupportedRestrictCongr
  generalize coverAuxiliaryPreimage_eq j T Z = h
  revert h
  generalize (b ⁻¹ᵁ (j ⁻¹ᵁ Z)) = A
  intro h
  subst A
  rfl

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [CompactSpace T.toScheme]

/-- Membership in the supported degree-zero restriction image is reflected on the overlap. -/
theorem restrict_mem_range_iff_of_cover (hZ : IsCompact (Z : Set X))
    (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (x : PerfectSupportedK (i ⁻¹ᵁ Z).ι 0) :
    KMap (overlapRestrict_exact j T Z) 0 x ∈
      (perfectSupportedKRestrict b (j ⁻¹ᵁ Z) 0).range ↔
    x ∈ (perfectSupportedKRestrict i Z 0).range := by
  let : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have hT : IsCompact (T : Set X) := isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace T.toScheme))
  let : CompactSpace W := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  let : Fact (HasDerivedRoofs i Z) := ⟨hasDerivedRoofs_of_qcqs i Z hZ⟩
  let : Fact (HasDerivedRoofs b (j ⁻¹ᵁ Z)) :=
    ⟨hasDerivedRoofs_of_qcqs b (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ)⟩
  let hi := hasPerfectComplements_of_qcqs i Z hZ
  let hb := hasPerfectComplements_of_qcqs b (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ)
  let di := denseCofiberData i Z Fact.out hi
  let db := denseCofiberData b (j ⁻¹ᵁ Z) Fact.out hb
  let : HasBinaryCoproducts (perfectSupported (i ⁻¹ᵁ Z).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen _)
  let : HasBinaryCoproducts (perfectSupported (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen _)
  change KMap (overlapRestrict_exact j T Z) 0 x ∈
      (KMap (perfectSupportedRestrict_exact b (j ⁻¹ᵁ Z)) 0).range ↔
    x ∈ (KMap (perfectSupportedRestrict_exact i Z) 0).range
  rw [← range_dense_inclusion_KMap_zero i Z hi,
    ← range_dense_inclusion_KMap_zero b (j ⁻¹ᵁ Z) hb]
  exact di.KMap_mem_inclusion_range_iff db (overlapRestrict_exact j T Z)
    (fun K => by
      change complexObjects i Z K.obj ↔ complexObjects b (j ⁻¹ᵁ Z)
        ((overlapRestrict j T Z).obj K).obj
      rw [overlapRestrict_obj]
      exact complexObjects_cover_iff j T Z hcover K.obj K.property)
    (targetFineJointData _ _) (targetFineJointData _ _)
    (targetFineJointData_section _ _) (targetFineJointData_section _ _) x

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
