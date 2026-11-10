module

import Colib.Algebra.Category.ModuleCat.QuotientSquare

open CategoryTheory
open scoped TensorProduct ChangeOfRings

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  (f : R →+* B) (φ : R →+* C) (ψ : C →+* D) (θ : B →+* D)
  (hsq : ψ.comp φ = θ.comp f) (hf : Function.Surjective f) (hψ : Function.Surjective ψ)
  (hker : RingHom.ker ψ = (RingHom.ker f).map φ)

-- Arbitrary common universe and only the quotient-square hypotheses.
example :
    (ModuleCat.extendScalars.{u, u, u} f).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) ≅
        (ModuleCat.restrictScalars θ).obj (ModuleCat.of D D) :=
  ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker

-- Both literal maps determine the forward formula.
example (b : B) (c : (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) :
    (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      (b ⊗ₜ[R, f] c) = θ b * ψ c := by
  simp

-- The inverse is computed on every coefficient image; ψ is surjective.
example (c : (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) :
    (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).inv (ψ c) =
      (1 : B) ⊗ₜ[R, f] c := by
  simp

-- A downstream cancellation identity uses the actual comparison formula.
example (b : B) (c : (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) :
    (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).inv (θ b * ψ c) =
      b ⊗ₜ[R, f] c :=
  ModuleCat.extendScalarsQuotientSquareIso_inv_mul f φ ψ θ hsq hf hψ hker b c

-- The square's two representatives give the same tensor, through the actual map.
example (r : R) (c : (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) :
    (f r) ⊗ₜ[R, f] c =
      (1 : B) ⊗ₜ[R, f]
        (id (α := (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))
          (@Mul.mul C _ (φ r) c)) := by
  apply (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).toLinearEquiv.injective
  change (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom _ =
    (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom _
  rw [ModuleCat.extendScalarsQuotientSquareIso_hom_tmul,
    ModuleCat.extendScalarsQuotientSquareIso_hom_tmul]
  change θ (f r) * ψ c = θ 1 * ψ (@Mul.mul C _ (φ r) c)
  have hr : ψ (φ r) = θ (f r) := congrArg (fun g : R →+* D => g r) hsq
  rw [map_one, one_mul]
  exact (congrArg (fun d : D => d * ψ c) hr.symm).trans
    (map_mul ψ (φ r) (show C from c)).symm

-- The native adjunction unit, not a separately stipulated unit map, becomes ψ.
example (c : (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) :
    (ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker).hom
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) c) = ψ c :=
  ModuleCat.extendScalarsQuotientSquareIso_hom_unit f φ ψ θ hsq hf hψ hker c
