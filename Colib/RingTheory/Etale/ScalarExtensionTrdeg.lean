/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Etale.PolynomialTrdeg
public import Colib.RingTheory.MvPolynomial.ScalarExtensionPushout

/-!
# Transcendence degree of an actual scalar-extended etale polynomial chart

Etaleness is preserved by scalar extension. The canonical polynomial tensor equivalence
identifies the extended variables, so every integral principal open has the original
coordinate count. This source was reconstructed after workspace loss; its final proof
steps are newly written and require fresh compilation.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra

private theorem etale_rightTensorProduct_map
    (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B]
    (f : A →ₐ[E] B) (hf : f.toRingHom.Etale) :
    (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Etale := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower E A B := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let : Algebra (A ⊗[E] L) (B ⊗[E] L) :=
    (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.toAlgebra
  have : IsScalarTower A B (B ⊗[E] L) := inferInstance
  have : IsScalarTower A (A ⊗[E] L) (B ⊗[E] L) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      simp only [Algebra.TensorProduct.algebraMap_apply]
      rfl
  have : Algebra.IsPushout A B (A ⊗[E] L) (B ⊗[E] L) :=
    Algebra.IsPushout.tensorProduct_tensorProduct E L A B (by
      ext x
      change Algebra.TensorProduct.map f (AlgHom.id E L) ((1 : A) ⊗ₜ[E] x) = 1 ⊗ₜ[E] x
      simp)
  exact RingHom.Etale.isStableUnderBaseChange A B (A ⊗[E] L) (B ⊗[E] L) hf

private theorem etale_leftTensorProduct_map
    (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B]
    (f : A →ₐ[E] B) (hf : f.toRingHom.Etale) :
    (Algebra.TensorProduct.map (AlgHom.id E L) f).toRingHom.Etale := by
  have h := RingHom.Etale.respectsIso.1 _ (Algebra.TensorProduct.comm E B L).toRingEquiv
    (RingHom.Etale.respectsIso.2 _ (Algebra.TensorProduct.comm E L A).toRingEquiv
      (etale_rightTensorProduct_map E L A B f hf))
  convert h using 1
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul l a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extending the coefficients of an actual etale polynomial chart and restricting to
an integral principal open preserves its exact transcendence degree. -/
theorem trdeg_localized_tensor_of_etale_polynomial_map
    (E L B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing B] [Algebra E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (e : L ⊗[E] B) [IsDomain (Localization.Away e)] :
    Algebra.trdeg L (Localization.Away e) = n := by
  let qL : MvPolynomial (Fin n) L →ₐ[L] L ⊗[E] B :=
    MvPolynomial.aeval fun i => (1 : L) ⊗ₜ[E] q (MvPolynomial.X i)
  have hq' : (MvPolynomial.aeval fun i => q (MvPolynomial.X i)) = q := by
    ext i
    simp
  have hL : qL.toRingHom.Etale := by
    have h := etale_leftTensorProduct_map E L _ B q hq
    rw [← hq', ← MvPolynomial.aeval_tensorComparison] at h
    have h' := RingHom.Etale.respectsIso.2 _
      (MvPolynomial.algebraTensorAlgEquiv E L).symm.toRingEquiv h
    convert h' using 1
    apply RingHom.ext
    intro p
    simp [qL]
  let j : L ⊗[E] B →ₐ[L] Localization.Away e :=
    IsScalarTower.toAlgHom L (L ⊗[E] B) (Localization.Away e)
  apply trdeg_eq_of_etale_polynomial_map (j.comp qL)
  exact RingHom.Etale.stableUnderComposition _ _ hL
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway e))

end Algebra
