/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.FiniteField.ScalarPresentation
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LargePrimeOriginalEtalePresentation

/-!
# Closed-point local vanishing over finite fields

Apply the two-prime presentation theorem to the identity étale map.
Each scalar presentation gives a zero neighborhood of the entire marked
scalar fibre. The two degrees are coprime, so the scalar transfers give
a zero neighborhood in the original affine scheme.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/FiniteField/AffineLocalVanishing.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `661437d4bc0a73dc4626792e534fc1571f0a167f`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open QuadraticIncidence.InfinityChart
open scoped TensorProduct

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A zero on the affine puncture extends to an affine zero neighborhood of a
closed point of a positive-dimensional smooth affine domain over a finite field. -/
theorem exists_finite_affine_zero_neighborhood_of_positive_trdeg
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (s : sections P (Cor.mk (affineSite k B)))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0) :
    ∃ O : (affineSite k B).left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      transfer P ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) s = 0 := by
  classical
  let ℓ := ringChar k
  let : Fact ℓ.Prime := ⟨CharP.prime_ringChar k⟩
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨n, m, hn, hm, hcoprime, hdata⟩ :=
    exists_two_prime_originalEtalePresentations k B ℓ x J hJ d hd (𝟙 _) a.left z
      (by simp only [Category.comp_id]; rfl) H ha hcover 0
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let E := ULift.{u} (FiniteField.Extension k ℓ n)
  let L := ULift.{u} (FiniteField.Extension k ℓ m)
  obtain ⟨hdegE, _, yE, _, huE, ⟨eE⟩⟩ := hdata n (Or.inl rfl)
  obtain ⟨hdegL, _, yL, _, huL, ⟨eL⟩⟩ := hdata m (Or.inr rfl)
  let : Algebra.Smooth E (B ⊗[k] E) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k E B)
  let : Algebra.Smooth L (B ⊗[k] L) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)
  have := @IsClosedImmersion.spec_of_quotient_mk (.of (B ⊗[k] E))
    (J.map (algebraMap B (B ⊗[k] E)))
  have := @IsClosedImmersion.spec_of_quotient_mk (.of (B ⊗[k] L))
    (J.map (algebraMap B (B ⊗[k] L)))
  obtain ⟨V, _, hxV, hzV⟩ := exists_scalar_zero_open_of_affine_presentation
    (L := E) a P hP s hs x yE huE _ _ _ eE
  obtain ⟨W, _, hxW, hzW⟩ := exists_scalar_zero_open_of_affine_presentation
    (L := L) a P hP s hs x yL huL _ _ _ eL
  have hdegrees : (Module.finrank k E).Coprime (Module.finrank k L) := by
    rw [hdegE, hdegL]
    exact hcoprime
  exact exists_affine_zero_open_of_coprime_scalar_zero_opens P (affineSite k B) s x
    V W hxV hxW hzV hzW hdegrees

end AlgebraicGeometry.PresheafWithTransfers
