/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.ScalarExtensionDescent
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Descent of the same affine coordinates and their principal opens

The native polynomial and principal-localization tensor equivalences identify the actual
scalar-extended evaluation maps. Their generator formulas, together with native faithfully
flat descent, descend properties on the unchanged coordinate tuple and localization element.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial
universe u
namespace MvPolynomial
variable (E L B : Type u) [Field E] [Field L] [Algebra E L]
 [CommRing B] [Algebra E B] {ι : Type} (g : ι → B)
/-- Evaluating the unchanged variables after extending coefficients preserves the original
tensor inclusion. -/
theorem aeval_map_includeRight (p : MvPolynomial ι E) :
    aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i) (map (algebraMap E L) p) =
      (1 : L) ⊗ₜ[E] aeval g p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [map_C, aeval_C, Algebra.TensorProduct.algebraMap_apply]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a
  | add p q hp hq => simp only [map_add, hp, hq, TensorProduct.tmul_add]
  | mul_X p i hp => simp [hp]
/-- The native polynomial tensor equivalence identifies the actual scalar-extended evaluation
map. -/
theorem aeval_tensorComparison :
    (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom.comp
      (algebraTensorAlgEquiv E L).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id E L) (aeval (R := E) g)).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul l p =>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, algebraTensorAlgEquiv_tmul,
      map_smul, aeval_map_includeRight, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.map_tmul, AlgHom.toRingHom_eq_coe,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]
/-- The native polynomial and localization tensor equivalences retain the original localized map. -/
theorem aevalAway_tensorComparison (r : B) :
    ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
      (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom).comp
      (algebraTensorAlgEquiv E L).toRingHom =
      (IsLocalization.Away.tensorProductEquivTMulRight E L r (Localization.Away r)).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id E L)
        ((IsScalarTower.toAlgHom E B (Localization.Away r)).comp
          (aeval (R := E) g))).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul l p =>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, algebraTensorAlgEquiv_tmul,
      map_smul, aeval_map_includeRight, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := E) (S := L) B r
      (Localization.Away r) l (aeval g p)).symm
  | add x y hx hy => simp only [map_add, hx, hy]
/-- A faithfully-flat descending property of the same coordinate map descends along a field
extension. -/
theorem of_aeval_scalarExtension
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (hf : P (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom) :
    P (aeval (R := E) g).toRingHom := by
  apply AlgHom.of_leftTensorProductMap_of_codescendsAlong P hP hi E L _ B (aeval (R := E) g)
  have h := hi.2 _ (algebraTensorAlgEquiv E L).toRingEquiv hf
  rwa [aeval_tensorComparison] at h
/-- Descent on the exact original principal-open coordinate map, with its localization element
unchanged. -/
theorem of_aevalAway_scalarExtension
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (r : B)
    (hf : P ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
      (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom)) :
    P ((algebraMap B (Localization.Away r)).comp (aeval (R := E) g).toRingHom) := by
  apply AlgHom.of_leftTensorProductMap_of_codescendsAlong P hP hi E L _ _
    ((IsScalarTower.toAlgHom E B (Localization.Away r)).comp (aeval (R := E) g))
  have h := hi.2 _ (algebraTensorAlgEquiv E L).toRingEquiv hf
  rw [aevalAway_tensorComparison] at h
  have h' := hi.1 _
    (IsLocalization.Away.tensorProductEquivTMulRight E L r
      (Localization.Away r)).symm.toRingEquiv h
  convert h' using 1
  apply RingHom.ext
  intro x
  simp
end MvPolynomial
