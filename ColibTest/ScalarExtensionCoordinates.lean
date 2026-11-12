/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Morphisms.Smooth.ScalarExtensionCoordinates
import Colib.AlgebraicGeometry.Limits.ScalarExtensionCoordinateFibers

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry CommRingCat MvPolynomial

universe u

/-- Relative dimension one descends on the original open at an actual intermediate field. -/
example (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [CommRing B] [Algebra K B] (d : ℕ) (g : Fin d → E ⊗[K] B) (r : E ⊗[K] B)
    [SmoothOfRelativeDimension 1 (Spec.map (ofHom
      ((algebraMap (L ⊗[K] B) (Localization.Away
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
        (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom)))] :
    SmoothOfRelativeDimension 1 (Spec.map (ofHom
      ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g).toRingHom))) :=
  smoothOfRelativeDimension_aevalAway_of_scalarTower K E L B g r 1

/-- Every original marking respects the actual localization and coefficient maps. -/
example (E L B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing B] [Algebra E B] (d : ℕ) (g : Fin d → B) (r : B)
    (T : Scheme.{u}) (ξ : T ⟶ Spec (.of (Localization.Away ((1 : L) ⊗ₜ[E] r)))) :
    (ξ ≫ Spec.map (ofHom (IsLocalization.Away.mapₐ (Localization.Away r)
      (Localization.Away ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r))
      (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r).toRingHom)) ≫
        Spec.map (ofHom ((algebraMap B (Localization.Away r)).comp
          (aeval (R := E) g).toRingHom)) =
    (ξ ≫ Spec.map (ofHom ((algebraMap (L ⊗[E] B)
      (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
      (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom))) ≫
        Spec.map (ofHom (MvPolynomial.map (algebraMap E L) :
          MvPolynomial (Fin d) E →+* MvPolynomial (Fin d) L)) := by
  rw [Category.assoc, Category.assoc]
  congr 1
  exact (isPullback_aevalAway_scalarExtension E L B g r).w


/-- The original whole marked fiber descends, independently of the etale-open choice. -/
example
    (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [CommRing B] [Algebra K B] (d : ℕ) (g : Fin d → E ⊗[K] B)
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
      Q ∈ PrimeSpectrum.basicOpen r :=
  fiber_subset_basicOpen_of_aeval_scalarTower K E L B g P r hW
