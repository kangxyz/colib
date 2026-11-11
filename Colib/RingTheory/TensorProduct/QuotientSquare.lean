/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor products in a square of quotient maps

For a commutative square `ψ.comp φ = θ.comp f`, with `f` and `ψ` surjective and
`ker ψ = (ker f).map φ`, the native tensor product `B ⊗[R] C` is the actual
`B`-module `D` with scalar map `θ`. The comparison sends `b ⊗ c` to `θ b * ψ c`.
Neither flatness nor regularity of a sequence is required.

The proof composes native quotient equivalences and the native tensor/quotient
comparison, then uses surjectivity of `R → B` to retain the `B`-action.
The intermediate tensor/quotient equivalence is restricted from `R / ker f`
to `R` before composition; its scalar orientation is not identified with `C`.

Implementation providers at Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`:
- `Mathlib/RingTheory/TensorProduct/Quotient.lean:68-84`;
- `Mathlib/RingTheory/Ideal/Quotient/Operations.lean:551-564,777-784`;
- `Mathlib/RingTheory/TensorProduct/Maps.lean:610-629`;
- `Mathlib/Algebra/Algebra/Tower.lean:296-316`.

This supplies only the generic coefficient comparison needed in the migration
of Motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/IncidenceTorReduction.lean:33-124`.
It does not establish a geometric stalk square, a regular common list, or Tor vanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u

namespace Algebra.TensorProduct

section Algebras

variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [IsScalarTower R B D]

/-- The actual quotient coefficient algebra is the native tensor product.
Surjectivity of `R → B` upgrades the composed `R`-algebra comparison to a
`B`-algebra comparison for the given action on `D`. -/
def quotientSquareAlgEquiv (ψ : C →ₐ[R] D)
    (hf : Function.Surjective (algebraMap R B)) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R C)) :
    B ⊗[R] C ≃ₐ[B] D :=
  AlgEquiv.extendScalarsOfSurjective hf
    (((((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.trans
        (Ideal.quotientEquivAlgOfEq R hker)).trans
        ((quotIdealMapEquivQuotTensor C (RingHom.ker (algebraMap R B))).restrictScalars R)).trans
        (Algebra.TensorProduct.congr
          (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B) hf)
          (AlgEquiv.refl : C ≃ₐ[R] C))).symm)

/-- On the image of the coefficient map, the inverse is `c ↦ 1 ⊗ c`. -/
@[simp]
lemma quotientSquareAlgEquiv_symm_apply (ψ : C →ₐ[R] D)
    (hf : Function.Surjective (algebraMap R B)) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R C)) (c : C) :
    (quotientSquareAlgEquiv ψ hf hψ hker).symm (ψ c) = 1 ⊗ₜ[R] c := by
  simp [quotientSquareAlgEquiv]

/-- The comparison retains the coefficient map itself. -/
@[simp high]
lemma quotientSquareAlgEquiv_one_tmul (ψ : C →ₐ[R] D)
    (hf : Function.Surjective (algebraMap R B)) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R C)) (c : C) :
    quotientSquareAlgEquiv ψ hf hψ hker (1 ⊗ₜ[R] c) = ψ c := by
  apply (quotientSquareAlgEquiv ψ hf hψ hker).symm.injective
  simp

/-- The comparison is the specified multiplication map on elementary tensors. -/
@[simp]
lemma quotientSquareAlgEquiv_tmul (ψ : C →ₐ[R] D)
    (hf : Function.Surjective (algebraMap R B)) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R C)) (b : B) (c : C) :
    quotientSquareAlgEquiv ψ hf hψ hker (b ⊗ₜ[R] c) = algebraMap B D b * ψ c := by
  calc
    quotientSquareAlgEquiv ψ hf hψ hker (b ⊗ₜ[R] c) =
        quotientSquareAlgEquiv ψ hf hψ hker (b • (1 ⊗ₜ[R] c)) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = algebraMap B D b * ψ c := by
      rw [map_smul, quotientSquareAlgEquiv_one_tmul, Algebra.smul_def]

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/RingTheory/TensorProduct/Quotient.lean:68-84"
  "ingredient" "Native quotient-of-R tensor equivalence, restricted to R before composition"]
  quotientSquareAlgEquiv

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/RingTheory/Ideal/Quotient/Operations.lean:551-564,777-784"
  "ingredient" "Actual surjective-map kernel quotients and transport along equality of ideals"]
  quotientSquareAlgEquiv

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/RingTheory/TensorProduct/Maps.lean:610-629"
  "ingredient" "Native tensor congruence transports the first quotient factor to the actual B"]
  quotientSquareAlgEquiv

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Algebra/Tower.lean:296-316"
  "ingredient" "Surjectivity of R to B upgrades the R-algebra equivalence to the actual B-action"]
  quotientSquareAlgEquiv

end Algebras

section RingHoms

variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]

/-- The `B`-linear tensor/quotient comparison for four literal ring maps.
The scalar structures are induced by `f`, `φ`, and `θ`, not existentially
chosen algebra maps. The `R`-action on `D` used in the proof is `θ.comp f`,
which the square identifies with `ψ.comp φ`. -/
def quotientSquareLinearEquiv (f : R →+* B) (φ : R →+* C)
    (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
    (hf : Function.Surjective f) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ = (RingHom.ker f).map φ) :
    letI := f.toAlgebra
    letI := φ.toAlgebra
    letI := θ.toAlgebra
    B ⊗[R] C ≃ₗ[B] D := by
  letI := f.toAlgebra
  letI := φ.toAlgebra
  letI := θ.toAlgebra
  letI := (θ.comp f).toAlgebra
  letI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let ψₐ : C →ₐ[R] D :=
    { ψ with commutes' := fun r => congrArg (fun g : R →+* D => g r) hsq }
  exact (quotientSquareAlgEquiv ψₐ hf hψ hker).toLinearEquiv

/-- The literal-map comparison has the required elementary-tensor formula. -/
@[simp]
lemma quotientSquareLinearEquiv_tmul (f : R →+* B) (φ : R →+* C)
    (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
    (hf : Function.Surjective f) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ = (RingHom.ker f).map φ) (b : B) (c : C) :
    letI := f.toAlgebra
    letI := φ.toAlgebra
    letI := θ.toAlgebra
    quotientSquareLinearEquiv f φ ψ θ hsq hf hψ hker (b ⊗ₜ[R] c) = θ b * ψ c := by
  let := f.toAlgebra
  let := φ.toAlgebra
  let := θ.toAlgebra
  let := (θ.comp f).toAlgebra
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let ψₐ : C →ₐ[R] D :=
    { ψ with commutes' := fun r => congrArg (fun g : R →+* D => g r) hsq }
  exact quotientSquareAlgEquiv_tmul ψₐ hf hψ hker b c

/-- The inverse of the literal-map comparison retains every coefficient image. -/
@[simp]
lemma quotientSquareLinearEquiv_symm_apply (f : R →+* B) (φ : R →+* C)
    (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
    (hf : Function.Surjective f) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ = (RingHom.ker f).map φ) (c : C) :
    letI := f.toAlgebra
    letI := φ.toAlgebra
    letI := θ.toAlgebra
    (quotientSquareLinearEquiv f φ ψ θ hsq hf hψ hker).symm (ψ c) = 1 ⊗ₜ[R] c := by
  let := f.toAlgebra
  let := φ.toAlgebra
  let := θ.toAlgebra
  let := (θ.comp f).toAlgebra
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let ψₐ : C →ₐ[R] D :=
    { ψ with commutes' := fun r => congrArg (fun g : R →+* D => g r) hsq }
  exact quotientSquareAlgEquiv_symm_apply ψₐ hf hψ hker c

end RingHoms

end Algebra.TensorProduct
