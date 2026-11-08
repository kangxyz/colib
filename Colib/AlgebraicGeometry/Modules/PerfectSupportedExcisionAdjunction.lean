/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedExtensionByZero

/-! # The supported extension-by-zero adjunction

The actual chain adjunction restricts to supported native perfect complexes when the open
immersion and the auxiliary acyclicity open cover the scheme. Its unchanged unit and counit
satisfy the literal triangle identities. Exactness uses ambient Mono and QuasiIso, without
an auxiliary exact-category structure. Adapted from Quillen support ExcisionAdjunction
and SupportedOpen/Excision at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual extension by zero on native supported perfect complexes. -/
def perfectSupportedExtensionByZero : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory ⥤
    (perfectSupported T.ι).FullSubcategory :=
  (perfectSupported T.ι).lift ((perfectSupported (j ⁻¹ᵁ T).ι).ι ⋙ Complex.extensionByZero j)
    (fun K => perfectSupported_extensionByZero_of_cover j T hcover K.property)

/-- Extension by zero preserves the actual native supported Waldhausen structures. -/
theorem perfectSupportedExtensionByZero_exact :
    Waldhausen.IsExact (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq (perfectSupportedExtensionByZero j T hcover) := by
  let F := Complex.extensionByZero j
  let P := perfectSupported (j ⁻¹ᵁ T).ι
  let Q := perfectSupported T.ι
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes U.Modules) P (perfectSupported_cofibrationClosed (j ⁻¹ᵁ T).ι)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex U.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := U.Modules) f.hom := hf
    infer_instance
  · intro A B D Z i f g k hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes U.Modules) P (perfectSupported_cofibrationClosed (j ⁻¹ᵁ T).ι)
        hi h).map F

/-- The original chain adjunction unit on the supported full subcategory. -/
def perfectSupportedExcisionUnit : 𝟭 ((perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) ⟶
    perfectSupportedExtensionByZero j T hcover ⋙ perfectSupportedRestrict j T where
  app K := ObjectProperty.homMk ((Complex.extensionByZeroAdjunction j).unit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((Complex.extensionByZeroAdjunction j).unit.naturality f.hom)

/-- The original chain adjunction counit on the supported full subcategory. -/
def perfectSupportedExcisionCounit :
    perfectSupportedRestrict j T ⋙ perfectSupportedExtensionByZero j T hcover ⟶
      𝟭 ((perfectSupported T.ι).FullSubcategory) where
  app K := ObjectProperty.homMk ((Complex.extensionByZeroAdjunction j).counit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((Complex.extensionByZeroAdjunction j).counit.naturality f.hom)

/-- The genuine supported adjunction retains the original triangle identities. -/
def perfectSupportedExcisionAdjunction :
    perfectSupportedExtensionByZero j T hcover ⊣ perfectSupportedRestrict j T where
  unit := perfectSupportedExcisionUnit j T hcover
  counit := perfectSupportedExcisionCounit j T hcover
  left_triangle_components K := ObjectProperty.hom_ext _
    ((Complex.extensionByZeroAdjunction j).left_triangle_components K.obj)
  right_triangle_components K := ObjectProperty.hom_ext _
    ((Complex.extensionByZeroAdjunction j).right_triangle_components K.obj)

/-- The actual supported unit is a quasi-isomorphism. -/
theorem perfectSupportedExcisionUnit_weak
    (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
      ((perfectSupportedExcisionUnit j T hcover).app K) := by
  change QuasiIso ((Complex.extensionByZeroAdjunction j).unit.app K.obj)
  infer_instance

/-- The actual supported counit is a quasi-isomorphism. -/
theorem perfectSupportedExcisionCounit_weak (K : (perfectSupported T.ι).FullSubcategory) :
    (perfectSupportedWaldhausen T.ι).weq ((perfectSupportedExcisionCounit j T hcover).app K) :=
  extensionByZero_supported_counit_quasiIso j T hcover K.property

end AlgebraicGeometry.Scheme.Modules
