/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedExcisionAdjunction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps
public import Colib.KTheory.Waldhausen.WeakNaturalTransformationBased
public import Colib.KTheory.Waldhausen.Functoriality

/-! # Supported open-cover excision on actual S-realizations and connective K-groups

Actual restriction and extension by zero induce homotopy inverse realization maps and mutually
inverse K-maps in all natural degrees, including zero. No compactness or separation is used.
Adapted from Quillen SupportedOpen/Excision.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The original supported S-construction realization map is an actual
homotopy equivalence, with the original extension-by-zero realization inverse. -/
def perfectSupportedExcisionRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (perfectSupportedWaldhausen T.ι).Delooping
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).Delooping where
  toFun := (deloopingMap (perfectSupportedRestrict_exact j T)).hom
  invFun := (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom
  left_inv := by
    have h := weakNaturalTransformationRealizationHomotopy
      (perfectSupportedWaldhausen T.ι) (perfectSupportedWaldhausen T.ι)
      ((perfectSupportedRestrict_exact j T).comp (perfectSupportedExtensionByZero_exact j T hcover))
      (IsExact.id (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq)
      (perfectSupportedExcisionCounit j T hcover) (perfectSupportedExcisionCounit_weak j T hcover)
    rw [← Waldhausen.deloopingMap_comp_deloopingMap (perfectSupportedRestrict_exact j T)
      (perfectSupportedExtensionByZero_exact j T hcover), deloopingMap_id] at h
    exact ⟨h⟩
  right_inv := by
    have h := weakNaturalTransformationRealizationHomotopy
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
      (IsExact.id (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ
        T).ι).weq)
      ((perfectSupportedExtensionByZero_exact j T hcover).comp (perfectSupportedRestrict_exact j T))
      (perfectSupportedExcisionUnit j T hcover) (perfectSupportedExcisionUnit_weak j T hcover)
    rw [← Waldhausen.deloopingMap_comp_deloopingMap (perfectSupportedExtensionByZero_exact j
      T hcover)
      (perfectSupportedRestrict_exact j T), deloopingMap_id] at h
    exact ⟨h.symm⟩

@[simp] lemma perfectSupportedExcisionRealizationHomotopyEquiv_toFun :
    (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).toFun =
      (deloopingMap (perfectSupportedRestrict_exact j T)).hom := rfl

@[simp] lemma perfectSupportedExcisionRealizationHomotopyEquiv_invFun :
    (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).invFun =
      (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom := rfl

lemma perfectSupportedKRestrict_extensionByZero_leftInverse (n : ℕ) (x : PerfectSupportedK T.ι n) :
    KMap (perfectSupportedExtensionByZero_exact j T hcover) n (perfectSupportedKRestrict j T n x) =
      x := by
  have h := KMap_eq_of_weakNatTrans
    ((perfectSupportedRestrict_exact j T).comp (perfectSupportedExtensionByZero_exact j T hcover))
    (IsExact.id (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq)
    (perfectSupportedExcisionCounit j T hcover) (perfectSupportedExcisionCounit_weak j T hcover) n
  rw [← Waldhausen.KMap_comp_KMap,KMap_id] at h
  exact DFunLike.congr_fun h x

lemma perfectSupportedKRestrict_extensionByZero_rightInverse (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    perfectSupportedKRestrict j T n (KMap (perfectSupportedExtensionByZero_exact j T hcover) n x) =
      x := by
  have h := KMap_eq_of_weakNatTrans
    (IsExact.id (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ
      T).ι).weq)
    ((perfectSupportedExtensionByZero_exact j T hcover).comp (perfectSupportedRestrict_exact j T))
    (perfectSupportedExcisionUnit j T hcover) (perfectSupportedExcisionUnit_weak j T hcover) n
  rw [← Waldhausen.KMap_comp_KMap,KMap_id] at h
  exact (DFunLike.congr_fun h x).symm

/-- The literal original supported restriction is an equivalence in every
connective K-degree, including zero, with the actual extension-by-zero inverse. -/
def perfectSupportedExcisionKEquiv (n : ℕ) :
    PerfectSupportedK T.ι n ≃* PerfectSupportedK (j ⁻¹ᵁ T).ι n where
  toFun := perfectSupportedKRestrict j T n
  invFun := KMap (perfectSupportedExtensionByZero_exact j T hcover) n
  left_inv := perfectSupportedKRestrict_extensionByZero_leftInverse j T hcover n
  right_inv := perfectSupportedKRestrict_extensionByZero_rightInverse j T hcover n
  map_mul' := (perfectSupportedKRestrict j T n).map_mul

@[simp] lemma perfectSupportedExcisionKEquiv_apply (n : ℕ) (x : PerfectSupportedK T.ι n) :
    perfectSupportedExcisionKEquiv j T hcover n x = perfectSupportedKRestrict j T n x := rfl

@[simp] lemma perfectSupportedExcisionKEquiv_symm_apply (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    (perfectSupportedExcisionKEquiv j T hcover n).symm x =
      KMap (perfectSupportedExtensionByZero_exact j T hcover) n x := rfl

include hcover in
lemma perfectSupportedKRestrict_bijective_of_cover (n : ℕ) :
    Function.Bijective (perfectSupportedKRestrict j T n) :=
  (perfectSupportedExcisionKEquiv j T hcover n).bijective

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0332",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Excision.lean"
    "adaptation" "Actual realization inverse and all-natural supported K-equivalence"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedExcisionRealizationHomotopyEquiv
  AlgebraicGeometry.Scheme.Modules.perfectSupportedExcisionKEquiv
