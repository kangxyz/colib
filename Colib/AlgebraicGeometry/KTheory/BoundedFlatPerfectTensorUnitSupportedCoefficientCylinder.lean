/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientNormalization

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
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.right, ⊤))ˣ)

/-- The original normalized tensor-pullback transformation cylinder. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientCylinde\
    r.lean:32"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
def tensorSupportedPairNormalizedCylinder :
    sSet (boundedAboveFlatPerfectSupportedWaldhausen T.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).weq ⊗ Δ[1] ⟶
      sSet (boundedAboveFlatPerfectSupportedWaldhausen S.hom).cof
        (boundedAboveFlatPerfectSupportedWaldhausen S.hom).weq :=
  weakNaturalTransformationCylinder _ _ (tensorSupportedPair_exact p).rebase
    (tensorSupportedPair_exact p).rebase
    (normalizedWeakTransformation (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom)
    (normalizedWeakTransformation_weak (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom
      (fun _ => (boundedAboveFlatPerfectSupportedWaldhausen S.hom).weq_iso _ inferInstance))

/-- A genuine diagonal simplex of the actual normalized fixed coefficient cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientCylinde\
    r.lean:48"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
def tensorSupportedPairCoefficientSimplex (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectSupportedWaldhausen T.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).weq).obj n) (τ θ : (Δ[1]).obj n) :
    (doubleDiagonal (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).obj n :=
  ⟨tensorSupportedPairNormalizedCoefficientPrism p r A.val τ.down θ.down, by
    rw [tensorSupportedPairNormalizedCoefficientPrism_eq]
    exact ((tensorSupportedPairNormalizedCylinder p r).app n (A, τ)).property.postcomp
      (suspensionRow_exact (boundedAboveFlatPerfectSupportedWaldhausen S.hom) θ.down)⟩

/-- The entire actual cell is the original normalized unit prism with its first coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientCylinde\
    r.lean:58"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
theorem tensorSupportedPairCoefficientSimplex_eq (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectSupportedWaldhausen T.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).weq).obj n) (τ θ : (Δ[1]).obj n) :
    tensorSupportedPairCoefficientSimplex p r n A τ θ =
      (suspensionCylinder (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).app n
        ((tensorSupportedPairNormalizedCylinder p r).app n (A, τ), θ) := by
  apply Subtype.ext
  exact tensorSupportedPairNormalizedCoefficientPrism_eq p r A.val τ.down θ.down

/-- Assemble the actual normalized fixed-cell values into the original simplicial double cylinder.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientCylinde\
    r.lean:69"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
def tensorSupportedPairCoefficientCylinder :
    (sSet (boundedAboveFlatPerfectSupportedWaldhausen T.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).weq ⊗ Δ[1]) ⊗
      Δ[1] ⟶ doubleDiagonal (boundedAboveFlatPerfectSupportedWaldhausen S.hom) where
  app n := ↾fun z => tensorSupportedPairCoefficientSimplex p r n z.1.1 z.1.2 z.2
  naturality n m α := by
    ext z : 3
    have h := ConcreteCategory.congr_hom
      (((tensorSupportedPairNormalizedCylinder p r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).naturality α) z
    change tensorSupportedPairCoefficientSimplex p r m
        (((sSet (boundedAboveFlatPerfectSupportedWaldhausen T.hom).cof
          (boundedAboveFlatPerfectSupportedWaldhausen T.hom).weq).map α) z.1.1)
        (((Δ[1] : SSet).map α) z.1.2) (((Δ[1] : SSet).map α) z.2) =
      ((doubleDiagonal (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).map α)
        (tensorSupportedPairCoefficientSimplex p r n z.1.1 z.1.2 z.2)
    rw [tensorSupportedPairCoefficientSimplex_eq, tensorSupportedPairCoefficientSimplex_eq]
    exact h

/-- Equality of the whole simplicial fixed cell, including every quotient and nerve operator. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientCylinde\
    r.lean:89"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
theorem tensorSupportedPairCoefficientCylinder_eq :
    tensorSupportedPairCoefficientCylinder p r =
      (tensorSupportedPairNormalizedCylinder p r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectSupportedWaldhausen S.hom) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorSupportedPairCoefficientSimplex_eq p r n z.1.1 z.1.2 z.2

end AlgebraicGeometry.Scheme.Modules
