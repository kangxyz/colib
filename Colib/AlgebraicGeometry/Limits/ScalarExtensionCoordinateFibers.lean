/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.MvPolynomial.ScalarExtensionPushout
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Whole-fiber containment on the actual finite-stage coordinates

Every point of the original fiber lifts over the specified upstairs base point in a scheme
pullback. Hence containment of the whole upstairs fiber in the scalar extension of a
principal open descends to that same open. No identification of D(r) with a separately chosen
etale chart, rational-point hypothesis, or ideal-membership descent certificate is required.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MvPolynomial Algebra.TensorProduct

universe u

namespace AlgebraicGeometry.Scheme
variable {X' X Y' Y : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {p : Y' ⟶ Y}
/-- Whole-fiber containment descends at a specified upstairs base point in an actual pullback. -/
theorem fiber_subset_of_isPullback (h : IsPullback q f' f p) (y' : Y')
    (W : Set X) (hW : ∀ x' : X', f' x' = y' → q x' ∈ W) :
    ∀ x : X, f x = p y' → x ∈ W := by
  intro x hx
  obtain ⟨x', hq, hf⟩ := exists_preimage_of_isPullback h x y' hx
  simpa only [hq] using hW x' hf
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry
open CommRingCat
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)
/-- The original affine coordinate square over an intermediate field is cartesian. -/
theorem isPullback_aeval_scalarTower :
    IsPullback
      (Spec.map (ofHom (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)).toRingHom))
      (Spec.map (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom))
      (Spec.map (ofHom (aeval (R := E) g).toRingHom))
      (Spec.map (ofHom (MvPolynomial.map (algebraMap E L) :
        MvPolynomial ι E →+* MvPolynomial ι L))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (MvPolynomial.isPushout_aeval_scalarTower K E L B g)

/-- The whole marked fiber remains inside the same descended principal open. -/
theorem fiber_subset_basicOpen_of_aeval_scalarTower
    (P : Spec (.of (L ⊗[K] B))) (r : E ⊗[K] B)
    (hW : ∀ Q : Spec (.of (L ⊗[K] B)),
      Spec.map (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom) Q =
      Spec.map (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom) P →
      Q ∈ PrimeSpectrum.basicOpen
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r)) :
    ∀ Q : Spec (.of (E ⊗[K] B)),
      Spec.map (ofHom (aeval (R := E) g).toRingHom) Q =
        Spec.map (ofHom (aeval (R := E) g).toRingHom)
          (Spec.map (ofHom (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)).toRingHom) P) →
      Q ∈ PrimeSpectrum.basicOpen r := by
  have h := isPullback_aeval_scalarTower K E L B g
  intro Q hQ
  apply Scheme.fiber_subset_of_isPullback h
    (Spec.map (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom) P)
      {x : Spec (.of (E ⊗[K] B)) | r ∉ x.asIdeal} ?_ Q
  · simpa only [← Scheme.Hom.comp_apply, h.w] using hQ
  · intro Q' hQ'
    exact hW Q' hQ'
end AlgebraicGeometry
