/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.MvPolynomial.ScalarExtensionDescent
public import Colib.RingTheory.TensorProduct.FiniteSubfieldModels

/-!
# Coordinates on the actual iterated scalar extension

The native cancellation equivalences identify L tensor E (E tensor K B), including its
principal localizations, with the original L tensor K B. Descent therefore applies to the
original image coordinates and opens at a chosen intermediate field, without replacing the
ambient affine scheme by an unidentified isomorphic model.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial Algebra.TensorProduct
universe u
namespace MvPolynomial
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)

/-- The canonical iterated scalar extension preserves evaluation of the original variables. -/
theorem aeval_map_cancelBaseChange (p : MvPolynomial ι E) :
    aeval (R := L) (fun i => Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))
      (MvPolynomial.map (algebraMap E L) p) =
    cancelBaseChange K E L L B ((1 : L) ⊗ₜ[E] aeval (R := E) g p) := by
  rw [← aeval_map_includeRight E L (E ⊗[K] B) g]
  change _ = (cancelBaseChange K E L L B).toAlgHom
    (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)
      (MvPolynomial.map (algebraMap E L) p))
  rw [MvPolynomial.comp_aeval_apply]
  change _ = aeval (R := L) (fun i => cancelBaseChange K E L L B
    ((1 : L) ⊗ₜ[E] g i)) (MvPolynomial.map (algebraMap E L) p)
  simp only [cancelBaseChange_includeRight]

/-- The original tensor inclusion, not a replacement algebra, gives the coordinate comparison. -/
theorem aeval_cancelBaseChange_comparison :
    (aeval (R := L) (fun i => Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom.comp
      (algebraTensorAlgEquiv E L).toRingHom =
      (cancelBaseChange K E L L B).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id E L) (aeval (R := E) g)).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul l p =>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, algebraTensorAlgEquiv_tmul, map_smul,
      aeval_map_cancelBaseChange, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.toRingHom_eq_coe]
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A native faithfully-flat descending property descends on the original iterated
scalar-extension model. -/
theorem of_aeval_scalarTower
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (hf : P (aeval (R := L) (fun i => Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom) :
    P (aeval (R := E) g).toRingHom := by
  apply AlgHom.of_leftTensorProductMap_of_codescendsAlong P hP hi E L _ _ (aeval (R := E) g)
  have h := hi.2 _ (algebraTensorAlgEquiv E L).toRingEquiv hf
  rw [aeval_cancelBaseChange_comparison] at h
  have h' := hi.1 _ (cancelBaseChange K E L L B).symm.toRingEquiv h
  convert h' using 1
  apply RingHom.ext
  intro x
  simp

/-- The canonical iterated scalar-extension localization comparison preserves the original
coordinate map. -/
theorem aevalAway_cancelBaseChange_comparison (r : E ⊗[K] B) :
    ((algebraMap (L ⊗[K] B) (Localization.Away
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
      (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom).comp
      (algebraTensorAlgEquiv E L).toRingHom =
      (cancelBaseChangeAway K E L B r).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id E L)
        ((IsScalarTower.toAlgHom E (E ⊗[K] B) (Localization.Away r)).comp
          (aeval (R := E) g))).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul l p =>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, algebraTensorAlgEquiv_tmul, map_smul, aeval_map_cancelBaseChange,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_apply]
    change _ = cancelBaseChangeAway K E L B r
      (l ⊗ₜ[E] algebraMap (E ⊗[K] B) (Localization.Away r) (aeval (R := E) g p))
    rw [cancelBaseChangeAway_tmul]
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Descent retains the exact original coordinate tuple and the image of its original
principal-open element. -/
theorem of_aevalAway_scalarTower
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (r : E ⊗[K] B)
    (hf : P ((algebraMap (L ⊗[K] B) (Localization.Away
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
      (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom)) :
    P ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp
      (aeval (R := E) g).toRingHom) := by
  apply AlgHom.of_leftTensorProductMap_of_codescendsAlong P hP hi E L _ _
    ((IsScalarTower.toAlgHom E (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g))
  have h := hi.2 _ (algebraTensorAlgEquiv E L).toRingEquiv hf
  rw [aevalAway_cancelBaseChange_comparison] at h
  have h' := hi.1 _ (cancelBaseChangeAway K E L B r).symm.toRingEquiv h
  convert h' using 1
  apply RingHom.ext
  intro x
  simp
end MvPolynomial
