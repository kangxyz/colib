/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.QuotientSquare
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual extension-of-scalars coefficients in a quotient square

This consumer identifies `extendScalars f (restrictScalars φ C)` with
`restrictScalars θ D`, preserving the actual four maps and computing the forward
and inverse maps on coefficient images. The unit of scalar extension followed by
the comparison is the literal map `ψ`. This is the coefficient object needed by
an every-degree Tor change-of-rings comparison; no Tor statement is assumed here.

The source is exactly Mathlib's native extension-of-scalars object, rather than
a separately defined tensor-product model. The module packaging uses Mathlib
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Mathlib/Algebra/Category/ModuleCat/Basic.lean:269-275` and
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:68-96,372-411,906-910`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat

variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  (f : R →+* B) (φ : R →+* C) (ψ : C →+* D) (θ : B →+* D)
  (hsq : ψ.comp φ = θ.comp f) (hf : Function.Surjective f) (hψ : Function.Surjective ψ)
  (hker : RingHom.ker ψ = (RingHom.ker f).map φ)

/-- Extension of the actual coefficient module is the actual quotient coefficient
with its literal `B`-action through `θ`. -/
def extendScalarsQuotientSquareIso :
    (extendScalars.{u, u, u} f).obj ((restrictScalars φ).obj (of C C)) ≅
      (restrictScalars θ).obj (of D D) := by
  letI := f.toAlgebra
  letI := φ.toAlgebra
  letI := θ.toAlgebra
  exact (Algebra.TensorProduct.quotientSquareLinearEquiv f φ ψ θ hsq hf hψ hker).toModuleIso

/-- Forward map on an elementary tensor in the actual extension object. -/
@[simp]
lemma extendScalarsQuotientSquareIso_hom_tmul (b : B)
    (c : (restrictScalars φ).obj (of C C)) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      (b ⊗ₜ[R, f] c) = θ b * ψ c := by
  exact Algebra.TensorProduct.quotientSquareLinearEquiv_tmul f φ ψ θ hsq hf hψ hker b c

/-- Inverse map on the actual image of `ψ`, not just an abstract inverse law. -/
@[simp]
lemma extendScalarsQuotientSquareIso_inv_apply
    (c : (restrictScalars φ).obj (of C C)) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).inv (ψ c) =
      (1 : B) ⊗ₜ[R, f] c := by
  exact Algebra.TensorProduct.quotientSquareLinearEquiv_symm_apply f φ ψ θ hsq hf hψ hker c

/-- The scalar-extension unit becomes the given coefficient quotient map. -/
lemma extendScalarsQuotientSquareIso_hom_one_tmul
    (c : (restrictScalars φ).obj (of C C)) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      ((1 : B) ⊗ₜ[R, f] c) = ψ c := by
  simp

/-- The actual native adjunction unit, followed by the comparison, is `ψ`
on elements of the original coefficient module. -/
lemma extendScalarsQuotientSquareIso_hom_unit
    (c : (restrictScalars φ).obj (of C C)) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      ((extendRestrictScalarsAdj f).unit.app ((restrictScalars φ).obj (of C C)) c) = ψ c := by
  rw [extendRestrictScalarsAdj_unit_app_apply]
  exact extendScalarsQuotientSquareIso_hom_one_tmul f φ ψ θ hsq hf hψ hker c

/-- The image of the first factor is the literal scalar map `θ`. -/
lemma extendScalarsQuotientSquareIso_hom_tmul_one (b : B) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      (b ⊗ₜ[R, f] (1 : C)) = θ b := by
  simp

/-- The inverse on a product computes the elementary tensor with both original
factors, providing a direct consumer of the multiplication formula. -/
lemma extendScalarsQuotientSquareIso_inv_mul (b : B)
    (c : (restrictScalars φ).obj (of C C)) :
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).inv (θ b * ψ c) =
      b ⊗ₜ[R, f] c := by
  rw [← extendScalarsQuotientSquareIso_hom_tmul f φ ψ θ hsq hf hψ hker b c]
  exact ConcreteCategory.congr_hom
    (extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom_inv_id _

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Category/ModuleCat/Basic.lean:269-275"
  "ingredient" "Package the constructed B-linear equivalence as a native module isomorphism"]
  extendScalarsQuotientSquareIso

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:68-96,372-411"
  "ingredient" "Actual restriction and extension objects with the literal ring-map actions"]
  extendScalarsQuotientSquareIso

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:906-910"
  "ingredient" "The native adjunction unit is one tensor c on each coefficient element"]
  extendScalarsQuotientSquareIso_hom_unit

end ModuleCat
