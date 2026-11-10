/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationSourceLeg
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Original Bass nullhomotopies under section evaluation

The proved positive-chart pasting and actual source-leg cone square compare the unchanged
strict and raw Laurent nullhomotopies, preserving every original cylinder parameter.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationNull.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original positive source leg, Laurent
unit and independent whole-homotopy parameters are retained in native objects. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.SectionBassEvaluationNull
variable (R : CommRingCat.{u})

/-- Original positive chart evaluation, with only its strict starting equality transported. -/
def positiveMovement :=
  (boundedAboveFlatAffineSectionChartFirstTrack R (CommRingCat.ofHom Polynomial.toLaurent)
    (coefficient_toLaurent R)).postcomp (mappingConeInclusion
      (boundedAboveFlatBassSquareComparison R))

/-- The original polynomial evaluation track followed by the raw positive Laurent leg. -/
def polynomialMovement :=
  (boundedAboveFlatAffineSectionChartSecondTrack R (CommRingCat.ofHom
    Polynomial.toLaurent)).postcomp
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))

/-- The unchanged Laurent coefficient evaluation track followed by raw cone inclusion. -/
def laurentMovement :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R)).postcomp
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))

/-- Original raw positive composition, preceded by the original base evaluation. -/
def newPositive :=
  ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatLaurentPlusHomotopy R)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))

/-- The actual positive-chart geometric equation retains its whole cone image. -/
def positivePasting :
    ((positiveMovement R).trans (polynomialMovement R)).RelHomotopy
      ((laurentMovement R).trans (newPositive R)) := by
  refine ((boundedAboveFlatAffineSectionChartFirstPasting R
    (CommRingCat.ofHom Polynomial.toLaurent) (coefficient_toLaurent R)).postcomp
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).ofLevels _ _ ?_ ?_
  · intro n
    exact congrArg (fun H => H.level n)
      (Homotopy.postcomp_trans
        (boundedAboveFlatAffineSectionChartFirstTrack R
          (CommRingCat.ofHom Polynomial.toLaurent) (coefficient_toLaurent R))
        (boundedAboveFlatAffineSectionChartSecondTrack R
          (CommRingCat.ofHom Polynomial.toLaurent))
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).symm
  · intro n
    have hOuter : boundedAboveFlatAffineSectionChartOuterTrack R
        (CommRingCat.ofHom Polynomial.toLaurent) (coefficient_toLaurent R) =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy
        (laurentCoefficientInclusion R)).trans
        ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
          (boundedAboveFlatLaurentPlusHomotopy R)).cast rfl
            (Category.assoc _ _ _).symm) := by
      exact congrArg (fun K =>
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy
          (laurentCoefficientInclusion R)).trans
          ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R) K).cast
            rfl (Category.assoc _ _ _).symm))
        (boundedAboveFlatAffineSectionChartGeometricTrack_plus R)
    have hPost := congrArg
      (fun H => H.postcomp (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)))
      hOuter
    have hWhole := hPost.trans (Homotopy.postcomp_trans
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R))
      ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatLaurentPlusHomotopy R)).cast rfl (Category.assoc _ _ _).symm)
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)))
    exact congrArg (fun H => H.level n) hWhole.symm

/-- The evaluated strict source leg traverses the original raw cone cylinder. -/
def oldCone : Homotopy
    (((boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R)) ≫
          mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (StrictSquare.sourceLeg (boundedAboveFlatAffineSectionBassSquare R) ≫
    boundedAboveFlatAffineSectionBassSpanEvaluation R)
    (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R))).cast
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x; rfl)
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x; rfl)

/-- The base evaluation followed by the raw source leg traverses that same cone cylinder. -/
def newCone : Homotopy
    (((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R)) ≫
          mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
    boundedAboveFlatBassSourceLeg R) (mappingConeHomotopy (boundedAboveFlatBassSquareComparison
      R))).cast
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x; rfl)
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x; rfl)

/-- The actual source-leg cone square supplies the whole polynomial-movement boundary. -/
def conePasting :
    (oldCone R).RelHomotopy ((polynomialMovement R).trans (newCone R)) := by
  let Z := Topology.LoopPrespectrum.Homotopy.refl
    (Topology.LoopPrespectrum.zeroHom (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)
      (mappingCone (boundedAboveFlatBassSquareComparison R)))
  have J : (oldCone R).RelHomotopy
      (((polynomialMovement R).trans (newCone R)).trans Z) := by
    refine (boundedAboveFlatAffineSectionBassSourceLegEvaluationConeBoundary R).ofLevels _ _ ?_ ?_
    · intro n; rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext; rintro ⟨s, x⟩; rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- Original geometric pasting combines with the cone movement without changing any track. -/
def pastedNullComparison :
    ((positiveMovement R).trans (oldCone R)).RelHomotopy
      ((laurentMovement R).trans ((newPositive R).trans (newCone R))) :=
  ((Homotopy.RelHomotopy.refl (positiveMovement R)).hcomp (conePasting R)).trans
    ((Homotopy.RelHomotopy.transAssoc _ _ _).symm.trans
      (((positivePasting R).hcomp (Homotopy.RelHomotopy.refl (newCone R))).trans
        (Homotopy.RelHomotopy.transAssoc _ _ _)))

/-- The unchanged strict nullhomotopy followed by the actual proved cone evaluation. -/
def originalOldNull : Homotopy
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))) ≫
        mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
          (Topology.LoopPrespectrum.zeroHom _ _) :=
  ((boundedAboveFlatAffineSectionBassNullHomotopy R).postcomp
    (boundedAboveFlatAffineSectionBassConeEvaluation R)).cast
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact congrArg
          (fun f => f.map n
            ((boundedAboveFlatAffineSectionPrespectrumFunctor.map
              (laurentCoefficientInclusion R)).map n x))
          (boundedAboveFlatAffineSectionBassConeEvaluation_inclusion R))
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x
          exact (boundedAboveFlatAffineSectionBassConeEvaluation R).map_point n)

/-- The unchanged raw nullhomotopy preceded by the actual original base evaluation. -/
def originalNewNull : Homotopy
    ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R)) ≫
        mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
          (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatBassLaurentNullHomotopy R)).cast (Category.assoc _ _ _).symm
      (by apply Topology.LoopPrespectrum.Hom.ext; funext n; ext x; rfl)

/-- Every original raw-null coordinate retains its positive track and actual cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull R).level n = ((newPositive R).trans (newCone R)).level n := by
  calc
    (originalNewNull R).level n =
        (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
          (boundedAboveFlatBassLaurentNullHomotopy R)).level n :=
      Homotopy.cast_level _ _ _ n
    _ = ((newPositive R).trans (newCone R)).level n := by
      change ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        ((boundedAboveFlatLaurentPlusHomotopy R).postcomp
          (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)))).trans
          (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
            (Homotopy.precomp (boundedAboveFlatBassSourceLeg R)
              (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R))))).level n = _
      apply Homotopy.trans_level_congr <;> rfl

/-- The original strict-null image retains the full comparison track and raw cone coordinate. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull R).level n = ((positiveMovement R).trans (oldCone R)).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  rfl

/-- The unchanged original Laurent nullhomotopies compare along actual Laurent evaluation. -/
def originalNullComparison :
    (originalOldNull R).RelHomotopy ((laurentMovement R).trans (originalNewNull R)) := by
  refine (pastedNullComparison R).ofLevels _ _ (originalOldNull_level R) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level R n

end AlgebraicGeometry.Scheme.Modules.SectionBassEvaluationNull

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationNull.lean:33-164"
  "adaptation" "Comparison of the unchanged strict and raw nulls along original Laurent evaluation"]
  AlgebraicGeometry.Scheme.Modules.SectionBassEvaluationNull.originalNullComparison
