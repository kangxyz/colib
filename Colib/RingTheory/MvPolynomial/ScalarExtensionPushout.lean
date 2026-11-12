/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.Ring.ScalarExtension
public import Colib.RingTheory.MvPolynomial.ScalarTowerDescent

/-!
# Actual localized coordinate pushout squares

The canonical polynomial and localization tensor comparisons give pushouts with the original
localization maps. The iterated scalar-extension case retains the original ambient tensor algebra.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MvPolynomial Algebra.TensorProduct

universe u

namespace MvPolynomial
open CommRingCat
variable (E L B : Type u) [Field E] [Field L] [Algebra E L]
 [CommRing B] [Algebra E B] {ι : Type} (g : ι → B)
/-- The original localized coordinate maps form their native scalar-extension pushout. -/
theorem isPushout_aevalAway_scalarExtension (r : B) :
    IsPushout
      (ofHom ((algebraMap B (Localization.Away r)).comp (aeval (R := E) g).toRingHom))
      (ofHom (MvPolynomial.map (algebraMap E L) : MvPolynomial ι E →+* MvPolynomial ι L))
      (ofHom (IsLocalization.Away.mapₐ (Localization.Away r)
        (Localization.Away ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r))
        (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r).toRingHom)
      (ofHom ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
        (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom)) := by
  apply (CommRingCat.isPushout_scalarExtension_map E L _ _
    ((IsScalarTower.toAlgHom E B (Localization.Away r)).comp (aeval (R := E) g))).of_iso
      (Iso.refl _) (Iso.refl _)
      (algebraTensorAlgEquiv E L).toCommRingCatIso
      (IsLocalization.Away.tensorProductEquivTMulRight E L r
        (Localization.Away r)).toCommRingCatIso
  · apply CommRingCat.hom_ext
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change algebraTensorAlgEquiv E L ((1 : L) ⊗ₜ[E] p) =
      MvPolynomial.map (algebraMap E L) p
    simp
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro b
    change IsLocalization.Away.tensorProductEquivTMulRight E L r (Localization.Away r)
      ((1 : L) ⊗ₜ[E] algebraMap B (Localization.Away r) b) = _
    rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
    change _ = IsLocalization.Away.mapₐ (Localization.Away r)
      (Localization.Away ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r))
      (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r
      (algebraMap B (Localization.Away r) b)
    simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  · exact (CommRingCat.hom_ext (aevalAway_tensorComparison E L B g r)).symm
end MvPolynomial

namespace MvPolynomial
open CommRingCat
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)
/-- The original intermediate-field localization map gives the actual coordinate pushout. -/
theorem isPushout_aevalAway_scalarTower (r : E ⊗[K] B) :
    IsPushout
      (ofHom ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g).toRingHom))
      (ofHom (MvPolynomial.map (algebraMap E L) : MvPolynomial ι E →+* MvPolynomial ι L))
      (ofHom (IsLocalization.Away.mapₐ (Localization.Away r)
        (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)) r).toRingHom)
      (ofHom ((algebraMap (L ⊗[K] B) (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
        (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom)) := by
  apply (CommRingCat.isPushout_scalarExtension_map E L _ _
    ((IsScalarTower.toAlgHom E (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g))).of_iso
      (Iso.refl _) (Iso.refl _)
      (algebraTensorAlgEquiv E L).toCommRingCatIso
      (Algebra.TensorProduct.cancelBaseChangeAway K E L B r).toCommRingCatIso
  · apply CommRingCat.hom_ext
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change algebraTensorAlgEquiv E L ((1 : L) ⊗ₜ[E] p) =
      MvPolynomial.map (algebraMap E L) p
    simp
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro b
    change Algebra.TensorProduct.cancelBaseChangeAway K E L B r
      ((1 : L) ⊗ₜ[E] algebraMap (E ⊗[K] B) (Localization.Away r) b) = _
    rw [Algebra.TensorProduct.cancelBaseChangeAway_tmul,
      Algebra.TensorProduct.cancelBaseChange_includeRight]
    change _ = IsLocalization.Away.mapₐ (Localization.Away r)
      (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)) r
      (algebraMap (E ⊗[K] B) (Localization.Away r) b)
    simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  · exact (CommRingCat.hom_ext (aevalAway_cancelBaseChange_comparison K E L B g r)).symm
end MvPolynomial

namespace MvPolynomial
open CommRingCat
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)
/-- The unchanged affine coordinates form the actual intermediate-field pushout. -/
theorem isPushout_aeval_scalarTower :
    IsPushout (ofHom (aeval (R := E) g).toRingHom)
      (ofHom (MvPolynomial.map (algebraMap E L) : MvPolynomial ι E →+* MvPolynomial ι L))
      (ofHom (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)).toRingHom)
      (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom) := by
  apply (CommRingCat.isPushout_scalarExtension_map E L _ _ (aeval (R := E) g)).of_iso
    (Iso.refl _) (Iso.refl _) (algebraTensorAlgEquiv E L).toCommRingCatIso
    (cancelBaseChange K E L L B).toCommRingCatIso
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change algebraTensorAlgEquiv E L ((1 : L) ⊗ₜ[E] p) = MvPolynomial.map (algebraMap E L) p
    simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact cancelBaseChange_includeRight K E L B b
  · exact (CommRingCat.hom_ext (aeval_cancelBaseChange_comparison K E L B g)).symm
end MvPolynomial
