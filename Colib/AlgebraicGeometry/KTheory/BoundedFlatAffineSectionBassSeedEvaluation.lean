/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentEvaluationHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyConjugation
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Original strict and raw Bass seed evaluation

The original conjugated loops retain the actual Laurent-unit action and nullhomotopies.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeedEvaluation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original positive source leg, Laurent
unit and independent whole-homotopy parameters are retained in native objects. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.SectionBassSeedEvaluation
variable (R : CommRingCat.{u})

/-- The original strict section unit followed by Laurent evaluation and raw cone inclusion. -/
def oldUnit :=
  ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).postcomp
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))

/-- The original raw Laurent-unit loop between base evaluation and cone inclusion. -/
def newUnit :=
  (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (boundedAboveFlatLaurentUnitHomotopy R)).postcomp
      (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))

/-- The genuine original unit comparison retains its entire raw-cone image. -/
def unitPasting :
    ((oldUnit R).trans (SectionBassEvaluationNull.laurentMovement R)).RelHomotopy
      ((SectionBassEvaluationNull.laurentMovement R).trans (newUnit R)) := by
  refine ((boundedAboveFlatAffineSectionLaurentEvaluationUnitPasting R).postcomp
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).ofLevels _ _ ?_ ?_
  · intro n
    exact congrArg (fun H => H.level n)
      (Homotopy.postcomp_trans (boundedAboveFlatAffineSectionLaurentEvaluationOldUnit R)
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R))
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).symm
  · intro n
    exact congrArg (fun H => H.level n)
      (Homotopy.postcomp_trans
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R))
        (boundedAboveFlatAffineSectionLaurentEvaluationNewUnit R)
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).symm

/-- Both proved original comparisons identify the complete based conjugated loops. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (SectionBassEvaluationNull.laurentMovement R)
    (oldUnit R) (newUnit R) (SectionBassEvaluationNull.originalOldNull R)
    (SectionBassEvaluationNull.originalNewNull R) (unitPasting R)
    (SectionBassEvaluationNull.originalNullComparison R)

/-- Postcomposition and endpoint casts retain every point of the original conjugated loop. -/
private theorem postcompConjugate_level {E F G : Topology.LoopPrespectrum.{u}}
    {f : E ⟶ F} {f' : E ⟶ G} (U : Homotopy f f)
    (N : Homotopy f (Topology.LoopPrespectrum.zeroHom E F)) (h : F ⟶ G)
    (U' : Homotopy f' f') (N' : Homotopy f' (Topology.LoopPrespectrum.zeroHom E G))
    (n : ℕ) (hU : U'.level n = (U.postcomp h).level n)
    (hN : N'.level n = (N.postcomp h).level n) :
    (U'.conjugateToZero N').level n = ((U.conjugateToZero N).postcomp h).level n := by
  calc
    (U'.conjugateToZero N').level n =
        ((N.postcomp h).symm.trans ((U.postcomp h).trans (N.postcomp h))).level n :=
      Homotopy.trans_level_congr N'.symm (U'.trans N') (N.postcomp h).symm
        ((U.postcomp h).trans (N.postcomp h)) n
        (Homotopy.symm_level_congr N' (N.postcomp h) n hN)
        (Homotopy.trans_level_congr U' N' (U.postcomp h) (N.postcomp h) n hU hN)
    _ = ((U.conjugateToZero N).postcomp h).level n := by
      rw [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm,
        Homotopy.postcomp_trans]

/-- The source loop map is exactly the strict seed followed by the proved Bass evaluation map. -/
theorem source_eq :
    ((oldUnit R).conjugateToZero (SectionBassEvaluationNull.originalOldNull R)).zeroLoopMap =
      boundedAboveFlatAffineSectionBassSeedMap R ≫
        boundedAboveFlatAffineSectionBassStepEvaluation R := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit R).conjugateToZero (SectionBassEvaluationNull.originalOldNull R)).level n
    (s, x) =
    ((((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)))).conjugateToZero
        (boundedAboveFlatAffineSectionBassNullHomotopy R)).postcomp
          (boundedAboveFlatAffineSectionBassConeEvaluation R)).level n (s, x)
  apply DFunLike.congr_fun
  refine postcompConjugate_level
    ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
      (mappingConeInclusion (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))))
    (boundedAboveFlatAffineSectionBassNullHomotopy R)
    (boundedAboveFlatAffineSectionBassConeEvaluation R) (oldUnit R)
    (SectionBassEvaluationNull.originalOldNull R) n ?_ ?_
  · apply ContinuousMap.ext
    rintro ⟨t, y⟩
    exact (congrArg
      (fun f => f.map n ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (t, y)))
      (boundedAboveFlatAffineSectionBassConeEvaluation_inclusion R)).symm
  · rfl

/-- The target loop map is exactly original base evaluation followed by the raw transition. -/
theorem target_eq :
    ((newUnit R).conjugateToZero (SectionBassEvaluationNull.originalNewNull R)).zeroLoopMap =
      boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        boundedAboveFlatAffineBassTransition R := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit R).conjugateToZero (SectionBassEvaluationNull.originalNewNull R)).level n
    (s, x) =
    (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (((boundedAboveFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).conjugateToZero
          (boundedAboveFlatBassLaurentNullHomotopy R))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl


end AlgebraicGeometry.Scheme.Modules.SectionBassSeedEvaluation

namespace AlgebraicGeometry.Scheme.Modules

/-- Original strict seed evaluation agrees through a genuine whole homotopy with the raw
geometric Bass transition, using the original Laurent unit and both original null tracks. -/
def boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy (R : CommRingCat.{u}) :
    Homotopy
      (boundedAboveFlatAffineSectionBassSeedMap R ≫
        boundedAboveFlatAffineSectionBassStepEvaluation R)
      (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫ boundedAboveFlatAffineBassTransition R) :=
  (SectionBassSeedEvaluation.conjugateComparison R).zeroLoopMapHomotopy.cast
    (SectionBassSeedEvaluation.source_eq R) (SectionBassSeedEvaluation.target_eq R)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0502", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeedEvaluation.lean:28-110"
  "adaptation" "Original strict seed followed by actual Bass evaluation compares to evaluation \
    followed by original raw seed"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedEvaluationHomotopy
