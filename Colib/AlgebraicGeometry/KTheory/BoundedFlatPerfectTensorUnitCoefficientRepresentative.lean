/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientSingle
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakRelations

/-!
# The actual coefficient square and the original weak one-row representative

The actual single of the coefficient automorphism acts on the independently constructed
coefficient row. Transporting its two endpoints by the displayed zero/identity/zero row
isomorphism gives exactly the original `oneWeakArrow` of the forward unit automorphism.
This identifies the whole quotient/nerve square before applying any realization or K-one class map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Apply the actual degree-zero single to every map of the original coefficient automorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:31-35"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSingleAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientSingle X ≅ tensorUnitCoefficientSingle X :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerRight (tensorUnitCoefficientRowAutomorphism X r)
      (CochainComplex.singleFunctor X.Modules 0))

/-- Faithful inclusion retains the actual single map at each coefficient interval position. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:38-44"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingleAutomorphism_original (X : Scheme.{u})
    (r : (Γ(X, ⊤))ˣ) (p : Interval ⦋1⦌) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((tensorUnitCoefficientSingleAutomorphism X r).hom.app p) =
      (CochainComplex.singleFunctor X.Modules 0).map
        ((tensorUnitCoefficientRowAutomorphism X r).hom.app p) := by
  simp only [tensorUnitCoefficientSingleAutomorphism, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]

/-- The coefficient single and canonical rank-one row have the same entire forward unit square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:47-65"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingleAutomorphism_comparison (X : Scheme.{u})
    (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitCoefficientSingleAutomorphism X r).hom ≫ (tensorUnitCoefficientSingleIso X).hom =
      (tensorUnitCoefficientSingleIso X).hom ≫
        ((oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).map
          (boundedAboveFlatRankOneUnit X r).hom).hom := by
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact (tensorUnitCoefficientSingle_zero X 0).eq_of_src _ _
  | change (tensorUnitCoefficientSingleAutomorphism X r).hom.app
        (interval 0 1 (by decide)) ≫ 𝟙 _ = 𝟙 _ ≫ (boundedAboveFlatRankOneUnit X r).hom
    simp only [Category.comp_id, Category.id_comp]
    apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
    rw [tensorUnitCoefficientSingleAutomorphism_original]
    rfl

/-- The displayed actual zero isomorphisms normalize the original coefficient-row square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:68-73"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientNormalizedArrow (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj
      (boundedAboveFlatRankOne X) ⟶
      (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj
      (boundedAboveFlatRankOne X) :=
  (objects (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).homMk
    ((tensorUnitCoefficientSingleIso X).inv ≫
      (tensorUnitCoefficientSingleAutomorphism X r).hom ≫ (tensorUnitCoefficientSingleIso X).hom)

/-- Normalization gives exactly the original one-row map of the original forward unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:76-84"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientNormalizedArrow_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientNormalizedArrow X r =
      (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).map
      (boundedAboveFlatRankOneUnit X r).hom := by
  apply ObjectProperty.hom_ext
  change (tensorUnitCoefficientSingleIso X).inv ≫
      ((tensorUnitCoefficientSingleAutomorphism X r).hom ≫
        (tensorUnitCoefficientSingleIso X).hom) = _
  rw [tensorUnitCoefficientSingleAutomorphism_comparison]
  simp

/-- The original coefficient square is pointwise weak after its displayed zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:87-94"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientWeakArrow (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (⟨(oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj
      (boundedAboveFlatRankOne X)⟩ : WeakRows (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      ⦋1⦌) ⟶
    ⟨(oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj
      (boundedAboveFlatRankOne X)⟩ :=
  ⟨tensorUnitCoefficientNormalizedArrow X r, by
    rw [tensorUnitCoefficientNormalizedArrow_eq]
    exact (oneEmbedding_exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).weak _
      ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)⟩

/-- The weak coefficient arrow is the pre-existing original automorphism representative. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:97-102"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientWeakArrow_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientWeakArrow X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).oneWeakArrow
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) := by
  apply WideSubcategory.hom_ext
  exact tensorUnitCoefficientNormalizedArrow_eq X r

/-- The entire original coefficient quotient/nerve square, not merely its middle automorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:105-110"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSquare (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (sSet (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq) _⦋1⦌ :=
  ⟨weakChainToGrid (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (ComposableArrows.mk₁ (tensorUnitCoefficientWeakArrow X r)),
    (isSimplex₂_diagonal_iff _ _ _).mp
      (weakChainToGrid_isSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) _)⟩

/-- The normalized tensor coefficient square is exactly the original forward weak-object square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientRepresentative.lean:113-120"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSquare_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientSquare X r =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weakObjectSimplex
      (boundedAboveFlatRankOneUnit X r).hom
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance) := by
  apply Subtype.ext
  change weakChainToGrid _ (ComposableArrows.mk₁ _) = _
  rw [tensorUnitCoefficientWeakArrow_eq]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0556"] tensorUnitCoefficientSquare_eq

end AlgebraicGeometry.Scheme.Modules
