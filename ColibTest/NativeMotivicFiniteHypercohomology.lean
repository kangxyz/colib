/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.PresheafWithTransfers

universe w u
variable (k : Type u) [Field k]

example (q n : ℕ) : motivicFiniteBaseComplex k q n ≅
    CochainComplex.finiteCoefficients (motivicBaseComplex k q) n :=
  motivicFiniteBaseComplexIso k q n

example (p : ℤ) (q n : ℕ) : (motivicBaseCoefficientShortComplex k p q n).ShortExact :=
  motivicBaseCoefficientShortComplex_shortExact k p q n

example (p : ℤ) (q n : ℕ) {A : AddCommGrpCat.{u + 1}}
    (x : A ⟶ (CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).X p)
    (hx : x ≫ (CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).d p (p + 1) = 0) :
    (CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).liftCycles x (p + 1)
        ((ComplexShape.up ℤ).next_eq' rfl) hx ≫
      (CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).homologyπ p ≫
        CochainComplex.finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n p =
    (motivicBaseComplex k q).liftCycles
        (x ≫ CochainComplex.finiteCoefficients.b (motivicBaseComplex k q) n p) (p + 1 + 1)
        ((ComplexShape.up ℤ).next_eq' rfl)
        (CochainComplex.finiteCoefficients.cycle_b (motivicBaseComplex k q) n p x hx) ≫
      (motivicBaseComplex k q).homologyπ (p + 1) :=
  CochainComplex.finiteCoefficients.bocksteinHomology_liftCycles
    (motivicBaseComplex k q) n p x hx

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

-- The sole additional hypothesis is the original ordinary derived-category universe.
example (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) ≃+
      (CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).homology p :=
  motivicFiniteBaseConeComparison k p q n

example (p : ℤ) (q n : ℕ) :
    Function.Exact (fun x : motivicCohomology k p q (SmoothSite.base (Spec (.of k))) =>
      n • x) (motivicBaseIntegralReduction k p q n) :=
  motivicBase_exact_mul_reduction k p q n

example (p : ℤ) (q n : ℕ) :
    Function.Exact (motivicBaseIntegralReduction k p q n) (motivicBaseBockstein k p q n) :=
  motivicBase_exact_reduction_bockstein k p q n

example (p : ℤ) (q n : ℕ) :
    Function.Exact (motivicBaseBockstein k p q n)
      (fun x : motivicCohomology k (p + 1) q (SmoothSite.base (Spec (.of k))) => n • x) :=
  motivicBase_exact_bockstein_mul k p q n

example (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteBaseConeComparison k p q n (motivicBaseIntegralReduction k p q n x) =
      CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k q) n p
        (motivicBaseEvaluationComparison k p q x) :=
  motivicBaseIntegralReduction_comparison k p q n x

example (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseEvaluationComparison k (p + 1) q (motivicBaseBockstein k p q n x) =
      CochainComplex.finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n p
        (motivicFiniteBaseConeComparison k p q n x) :=
  motivicBaseBockstein_comparison k p q n x

example (p : ℤ) (q : ℕ) :
    Subsingleton (motivicFiniteCohomology k p q 1 (SmoothSite.base (Spec (.of k)))) :=
  subsingleton_motivicFiniteCohomology_base_one k p q

example (p : ℤ) (q : ℕ) :
    Function.Exact (motivicBaseIntegralReduction k p q 0) (motivicBaseBockstein k p q 0) :=
  motivicBase_exact_reduction_bockstein k p q 0

example (p : ℤ) (q n : ℕ) {X Y Z : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    motivicFiniteCohomologyRestriction k p q n (f ≫ g) =
      motivicFiniteCohomologyRestriction k p q n g ≫
        motivicFiniteCohomologyRestriction k p q n f :=
  motivicFiniteCohomologyRestriction_comp k p q n f g
