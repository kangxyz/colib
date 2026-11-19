/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor

/-!
# Literal tensor extension of idempotent images

The universal tensor comparison for an actual matrix image sends a pure tensor
to the vector with coordinates `f (x i) * s`. Its inverse is the sum of tensors
of the original idempotent columns with the new coefficients. The comparison
is natural for every compatible rectangular matrix and recovers the canonical
comparison for arbitrary finite projectives through their actual presentation.

## Implementation provenance

Adapted from the Quillen source
`Quillen/Aglib/Algebra/Category/ModuleCat/MatrixImageTensor.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MulOpposite

namespace Matrix.RightModule

open RightScalarExtension

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S) (P : ProjectiveMatrices R)

/-- Extend the matrix-image unit through the literal balanced tensor. -/
def tensorImageForward :
    Tensor f (linearMap P.p).range →ₗ[Sᵐᵒᵖ] (linearMap (P.p.map f)).range :=
  lift f (imageUnit f P)

/-- Extend the tensor unit through the actual mapped idempotent image. -/
def tensorImageBackward :
    (linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] Tensor f (linearMap P.p).range :=
  imageExtensionLift f P (Tensor f (linearMap P.p).range) (unit f)

lemma tensorImageForward_unit (x : (linearMap P.p).range) :
    tensorImageForward f P (unit f x) = imageUnit f P x :=
  lift_unit f (imageUnit f P) x

@[simp] lemma tensorImageBackward_unit (x : (linearMap P.p).range) :
    tensorImageBackward f P (imageUnit f P x) = unit f x :=
  imageExtensionLift_unit f P (Tensor f (linearMap P.p).range) (unit f) x

/-- The canonical equivalence between the tensor of an image and the mapped image. -/
def tensorImageEquiv :
    Tensor f (linearMap P.p).range ≃ₗ[Sᵐᵒᵖ] (linearMap (P.p.map f)).range :=
  LinearEquiv.ofLinearMap (tensorImageForward f P) (tensorImageBackward f P)
    (by
      apply (imageExtensionHomEquiv f P (linearMap (P.p.map f)).range).injective
      apply LinearMap.ext
      intro x
      change tensorImageForward f P (tensorImageBackward f P (imageUnit f P x)) =
        imageUnit f P x
      rw [tensorImageBackward_unit, tensorImageForward_unit])
    (by
      apply hom_ext_unit f
      intro x
      change tensorImageBackward f P (tensorImageForward f P (unit f x)) = unit f x
      rw [tensorImageForward_unit, tensorImageBackward_unit])

lemma tensorImageEquiv_unit (x : (linearMap P.p).range) :
    tensorImageEquiv f P (unit f x) = imageUnit f P x :=
  tensorImageForward_unit f P x

/-- The comparison uses the conventional right multiplication order on every coordinate. -/
@[simp, colib_tag "COL-1317", colib_ref "quillen"
  "Quillen/Aglib/Algebra/Category/ModuleCat/MatrixImageTensor.lean:78-80" "adaptation"
  "The map on an actual matrix-image generator has the indicated right coefficient order."]
lemma tensorImageEquiv_pure_apply (x : (linearMap P.p).range) (s : S)
    (i : Fin P.X.rank) :
    (tensorImageEquiv f P (pure f x s)).val i = f (x.val i) * s := rfl

/-- The actual column of the idempotent, considered as an element of its image. -/
def imageColumn (i : Fin P.X.rank) : (linearMap P.p).range :=
  (linearMap P.p).rangeRestrict (Pi.single i 1)

@[simp] lemma imageColumn_apply (i j : Fin P.X.rank) :
    (imageColumn P i).val j = P.p j i := by
  change linearMap P.p (Pi.single i 1) j = P.p j i
  simp [linearMap_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The inverse comparison is the sum of original image columns with right coefficients. -/
@[colib_tag "COL-1317", colib_ref "quillen"
  "Quillen/Aglib/Algebra/Category/ModuleCat/MatrixImageTensor.lean:92-96" "adaptation"
  "The inverse is the actual sum of idempotent columns with right coefficients."]
lemma tensorImageEquiv_symm_apply (y : (linearMap (P.p.map f)).range) :
    (tensorImageEquiv f P).symm y = ∑ i, pure f (imageColumn P i) (y.val i) := by
  change (∑ i, op (y.val i) • unit f (imageColumn P i)) =
    ∑ i, pure f (imageColumn P i) (y.val i)
  simp only [← pure_eq_smul_unit]

/-- The tensor/image comparison is natural for every compatible rectangular matrix. -/
lemma tensorImageEquiv_naturality {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    (tensorImageEquiv f Q).toLinearMap.comp (RightScalarExtension.map f (imageMap a)) =
      (imageMap ((baseChange f).map a)).comp (tensorImageEquiv f P).toLinearMap := by
  apply hom_ext_unit f
  intro x
  change tensorImageEquiv f Q (RightScalarExtension.map f (imageMap a) (unit f x)) =
    imageMap ((baseChange f).map a) (tensorImageEquiv f P (unit f x))
  rw [RightScalarExtension.map_unit, tensorImageEquiv_unit, tensorImageEquiv_unit]
  exact imageUnit_naturality f a x

end Matrix.RightModule

namespace ModuleCat.FiniteProjective

open RightScalarExtension

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The matrix formula is the same canonical comparison, through the actual presentation. -/
theorem rightTensorBaseChangeEquiv_presentation (f : R →+* S)
    (P : Category.{u, u} Rᵐᵒᵖ) :
    (Matrix.RightModule.tensorImageEquiv f
          (Matrix.RightModule.imageEquivalence.inverse.obj P)).toLinearMap.comp
        (RightScalarExtension.map f (rightBaseChangePresentationEquiv P).symm.toLinearMap) =
      (rightTensorBaseChangeEquiv f P).toLinearMap := by
  apply RightScalarExtension.hom_ext f
  intro p s
  exact (congrArg
    (Matrix.RightModule.tensorImageEquiv f (Matrix.RightModule.imageEquivalence.inverse.obj P))
    (RightScalarExtension.map_pure f
      (rightBaseChangePresentationEquiv P).symm.toLinearMap p s)).trans (by rfl)

end ModuleCat.FiniteProjective
