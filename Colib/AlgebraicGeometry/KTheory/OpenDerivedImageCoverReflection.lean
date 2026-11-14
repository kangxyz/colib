/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.CoverReflection
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.QcqsGeometry
public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCofinality
public import Colib.KTheory.Waldhausen.Cofinality.ImageReflection

/-! # Reflection of the degree-zero restriction image on a cover

The actual restriction image in (K_0) is reflected on the overlap of a
quasi-compact two-open cover of a quasi-separated scheme. This uses derived
gluing and the dense-image obstruction, not surjectivity onto (K_0) of either open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Cofinality

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) [CompactSpace T.toScheme]

local notation "jbase" => PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j))
local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map jbase) T
local notation "W" => Scheme.Opens.toScheme I₀
local notation "a" => Scheme.Hom.resLE j T I₀ le_rfl
local notation "b" => Scheme.Opens.ι I₀

local instance : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- A class on the first open is in the ambient restriction image precisely when
its restriction to the overlap is in the second open's restriction image. -/
theorem restrict_mem_range_iff_of_cover
    (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (x : (RingedSpace.perfectComplexesWaldhausen T.toScheme.toRingedSpace).K 0) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact a) 0 x ∈
      (KMap (perfectComplexesRestrictOpenImmersion_isExact b) 0).range ↔
    x ∈ (KMap (perfectComplexesRestrictOpenImmersion_isExact T.ι) 0).range := by
  let : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have hT : IsCompact (T : Set X) := isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace T.toScheme))
  let : CompactSpace W := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  let : Fact (HasDerivedRoofs T.ι) := ⟨hasDerivedRoofs_of_qcqs T.ι⟩
  let : Fact (HasDerivedRoofs b) := ⟨hasDerivedRoofs_of_qcqs b⟩
  let hT' := hasPerfectComplements_of_qcqs T.ι
  let hW := hasPerfectComplements_of_qcqs b
  let dT := denseCofiberData T.ι Fact.out hT'
  let dW := denseCofiberData b Fact.out hW
  let : HasBinaryCoproducts
      (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := T.toScheme.toRingedSpace))) :=
    Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen _)
  let : HasBinaryCoproducts
      (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := (W).toRingedSpace))) :=
    Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen _)
  rw [← range_dense_inclusion_KMap_zero T.ι hT', ← range_dense_inclusion_KMap_zero b hW]
  exact dT.KMap_mem_inclusion_range_iff dW
    (perfectComplexesRestrictOpenImmersion_isExact a)
    (fun E => complexObjects_cover_iff j T hcover E.obj E.property)
    (targetFineJointData _) (targetFineJointData _)
    (targetFineJointData_section _) (targetFineJointData_section _) x

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KZeroCover.lean:51-70"
  "adaptation" "Reflection of the actual degree-zero restriction image"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.restrict_mem_range_iff_of_cover
