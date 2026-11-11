/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientNormalization

/-!
# The simplicial fixed coefficient tensor cell

The independently constructed coefficient row, after its two explicit zero normalizations, is
assembled into a genuine double simplicial cylinder. The first interval is the forward unit
nerve edge and the second is its first coefficient S-row. Equality with the original normalized
transformation cylinder followed by the original suspension cylinder proves all simplicial
operators simultaneously. Neither interval is transposed or identified with the other.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
      CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The original normalized tensor-pullback transformation cylinder. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientCylinder.lean:32"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
def tensorUnitPullbackNormalizedCylinder :
    sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq ⊗ Δ[1] ⟶
      sSet (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq :=
  weakNaturalTransformationCylinder _ _ (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
    (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
    (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
    (normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullback_exact f)
      (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
      (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance))

/-- A genuine diagonal simplex of the actual normalized fixed coefficient cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientCylinder.lean:46"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
def tensorUnitPullbackCoefficientSimplex (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq).obj n) (τ θ : (Δ[1]).obj n) :
    (doubleDiagonal (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj n :=
  ⟨tensorUnitPullbackNormalizedCoefficientPrism f r A.val τ.down θ.down, by
    rw [tensorUnitPullbackNormalizedCoefficientPrism_eq]
    exact ((tensorUnitPullbackNormalizedCylinder f r).app n (A, τ)).property.postcomp
      (suspensionRow_exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ.down)⟩

/-- The entire actual cell is the original normalized unit prism with its first coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientCylinder.lean:56"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
theorem tensorUnitPullbackCoefficientSimplex_eq (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq).obj n) (τ θ : (Δ[1]).obj n) :
    tensorUnitPullbackCoefficientSimplex f r n A τ θ =
      (suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).app n
        ((tensorUnitPullbackNormalizedCylinder f r).app n (A, τ), θ) := by
  apply Subtype.ext
  exact tensorUnitPullbackNormalizedCoefficientPrism_eq f r A.val τ.down θ.down

/-- Assemble the actual normalized fixed-cell values into the original simplicial double cylinder.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientCylinder.lean:67"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
def tensorUnitPullbackCoefficientCylinder :
    (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq ⊗ Δ[1]) ⊗
      Δ[1] ⟶ doubleDiagonal (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) where
  app n := ↾fun z => tensorUnitPullbackCoefficientSimplex f r n z.1.1 z.1.2 z.2
  naturality n m α := by
    ext z : 3
    have h := ConcreteCategory.congr_hom
      (((tensorUnitPullbackNormalizedCylinder f r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).naturality α) z
    change tensorUnitPullbackCoefficientSimplex f r m
        (((sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
          (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq).map α) z.1.1)
        (((Δ[1] : SSet).map α) z.1.2) (((Δ[1] : SSet).map α) z.2) =
      ((doubleDiagonal (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).map α)
        (tensorUnitPullbackCoefficientSimplex f r n z.1.1 z.1.2 z.2)
    rw [tensorUnitPullbackCoefficientSimplex_eq, tensorUnitPullbackCoefficientSimplex_eq]
    exact h

/-- Equality of the whole simplicial fixed cell, including every quotient and nerve operator. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientCylinder.lean:86"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
theorem tensorUnitPullbackCoefficientCylinder_eq :
    tensorUnitPullbackCoefficientCylinder f r =
      (tensorUnitPullbackNormalizedCylinder f r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorUnitPullbackCoefficientSimplex_eq f r n z.1.1 z.1.2 z.2

end AlgebraicGeometry.Scheme.Modules
