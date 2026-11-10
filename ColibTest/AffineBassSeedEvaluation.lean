/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeedEvaluation

/-! Native consumers for the actual affine Bass evaluation and original seed square.
No replacement square, null profile, unit or comparison is supplied by this consumer. -/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Topology unitInterval
universe u
variable (R : CommRingCat.{u})

example : Homotopy
    (boundedAboveFlatAffineSectionBassSeedMap R ≫
      boundedAboveFlatAffineSectionBassStepEvaluation R)
    (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatAffineBassTransition R) :=
  boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R

example (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).level (n + 1)
      (r, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) s =
    Path.toContinuousMap ((boundedAboveFlatAffineBassStep R).structureMap n
      ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).level n (r, x)) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).comm n r x t)

example (r s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level 0
      (r, HomotopyPushout.cylinder
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) 0 (s, x)) =
      (boundedAboveFlatAffineSectionBassEvaluationDescPasting R).toSquare.level 0
        (r, (s, x)) :=
  boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_cylinder R 0 r s x

example (n : ℕ) (r s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, HomotopyPushout.cylinder
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) n (s, x)) =
      (boundedAboveFlatAffineSectionBassEvaluationDescPasting R).toSquare.level n
        (r, (s, x)) :=
  boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_cylinder R n r s x

example (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inl
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))).map n x) =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom Polynomial.toLaurent)).level n (r, x) :=
  boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_inl R n r x

example (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inr
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))).map n x) =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom
          (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))).level n (r, x) :=
  boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy_inr R n r x

example : mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)) ≫
        boundedAboveFlatAffineSectionBassConeEvaluation R =
    boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)) ≫
      mappingConeInclusion (boundedAboveFlatBassSquareComparison R) :=
  boundedAboveFlatAffineSectionBassConeEvaluation_inclusion R

example (n : ℕ) (s : unitInterval)
    (x : (StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).space n) :
    (boundedAboveFlatAffineSectionBassConeEvaluation R).map n
      (ReducedMappingCone.cylinder
        ((StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).point n)
        ((boundedAboveFlatAffineSectionBassSquare R).right.right.point n)
        ((StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)).map n)
        (⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
        ((boundedAboveFlatAffineSectionBassComparisonEvaluationHomotopy R).level n (s, x)) :=
  mappingConeSquareMap_first_half _ _ _ _ _ n s x

example (n : ℕ) (s : unitInterval)
    (x : (StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).space n) :
    (boundedAboveFlatAffineSectionBassConeEvaluation R).map n
      (ReducedMappingCone.cylinder
        ((StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).point n)
        ((boundedAboveFlatAffineSectionBassSquare R).right.right.point n)
        ((StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)).map n)
        (⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level n
        (s, (boundedAboveFlatAffineSectionBassSpanEvaluation R).map n x) :=
  mappingConeSquareMap_second_half _ _ _ _ _ n s x

example (n : ℕ) (r s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare R).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level n
        (s, (boundedAboveFlatAffineSectionBassSourceLegEvaluationHomotopy R).level n (r, x)) :=
  boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare_apply R n r s x

example : (SectionBassEvaluationNull.originalOldNull R).RelHomotopy
    ((SectionBassEvaluationNull.laurentMovement R).trans
      (SectionBassEvaluationNull.originalNewNull R)) :=
  SectionBassEvaluationNull.originalNullComparison R

example : ((SectionBassSeedEvaluation.oldUnit R).conjugateToZero
      (SectionBassEvaluationNull.originalOldNull R)).zeroLoopMap =
    boundedAboveFlatAffineSectionBassSeedMap R ≫
      boundedAboveFlatAffineSectionBassStepEvaluation R :=
  SectionBassSeedEvaluation.source_eq R

example : ((SectionBassSeedEvaluation.newUnit R).conjugateToZero
      (SectionBassEvaluationNull.originalNewNull R)).zeroLoopMap =
    boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatAffineBassTransition R :=
  SectionBassSeedEvaluation.target_eq R

example (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).level n
      (0, x)) s =
      Path.toContinuousMap ((boundedAboveFlatAffineSectionBassStepEvaluation R).map n
        ((boundedAboveFlatAffineSectionBassSeedMap R).map n x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).at_zero n x)

example (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).level 0
      (1, x)) s =
      Path.toContinuousMap ((boundedAboveFlatAffineBassTransition R).map 0
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0 x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).at_one 0 x)

example (n : ℕ) (r s : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).level n
      (r, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) s =
      Path.toContinuousMap ((boundedAboveFlatAffineBassStep R).point n) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy R).at_point n r)

example (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (SectionBassEvaluationNull.originalNullComparison R).level (n + 1)
      (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (mappingCone (boundedAboveFlatBassSquareComparison R)).structureMap n
        ((SectionBassEvaluationNull.originalNullComparison R).level n (r, (s, x))) t :=
  (SectionBassEvaluationNull.originalNullComparison R).comm n r s x t

example (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassSpanEvaluation R).map n
      (HomotopyPushout.cylinder
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) n
        (⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      (HomotopyPushout.inl
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))).map n
        ((boundedAboveFlatAffineEvaluationCoefficientHomotopy
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).level n (s, x)) :=
  HomotopyPushout.mapOfHomotopies_first_half _ _ _ _ _ _ _ _ _ n s x

example (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) (r s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionChartFirstPasting R k h).level n (r, (s, x)) =
      ((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy
        (R := R) (S := .of (Polynomial R)) (T := .of (LaurentPolynomial R))
        (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).symm).level n (r, (s, x)) := rfl

example (n : ℕ) (r s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (SectionBassSeedEvaluation.unitPasting R).level n (r, (s, x)) =
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
        ((boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting R).level n (r, (s, x))) := rfl
