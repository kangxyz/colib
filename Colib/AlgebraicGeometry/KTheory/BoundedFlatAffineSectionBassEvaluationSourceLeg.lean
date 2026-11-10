/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluation
public import Colib.Topology.Prespectrum.HomotopySquareInterchange
public import Colib.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Original source-leg movement under section evaluation

The unchanged polynomial evaluation track moves the actual strict Bass source leg into its raw
geometric counterpart. Interchange with the original cone contraction retains both parameters.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationSourceLeg.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original positive source leg, Laurent
unit and independent whole-homotopy parameters are retained in native objects. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- Actual span evaluation retains the literal positive polynomial source endpoint. -/
theorem boundedAboveFlatAffineSectionBassSourceLeg_evaluation :
    StrictSquare.sourceLeg (boundedAboveFlatAffineSectionBassSquare R) ≫
      boundedAboveFlatAffineSectionBassSpanEvaluation R =
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
      →+* Polynomial R))) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
        HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  ext x
  rfl

/-- The original coefficient homotopy moves the actual source leg through the raw span. -/
def boundedAboveFlatAffineSectionBassSourceLegEvaluationHomotopy :
    Homotopy
      (StrictSquare.sourceLeg (boundedAboveFlatAffineSectionBassSquare R) ≫
        boundedAboveFlatAffineSectionBassSpanEvaluation R)
      (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫ boundedAboveFlatBassSourceLeg R) :=
  ((boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R →+*
    Polynomial R)))).postcomp
    (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)))).cast
        (boundedAboveFlatAffineSectionBassSourceLeg_evaluation R).symm (Category.assoc _ _ _)

/-- The original source-leg movement through the unchanged raw cone nullhomotopy. -/
def boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare :=
  Homotopy.Square.interchange (boundedAboveFlatAffineSectionBassSourceLegEvaluationHomotopy R)
    (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R))

/-- Both original polynomial and cone parameters remain independent. -/
theorem boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare_apply (n : ℕ)
    (r s : unitInterval) (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare R).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level n
        (s, (boundedAboveFlatAffineSectionBassSourceLegEvaluationHomotopy R).level n (r, x)) := rfl

/-- The actual interchange square supplies its whole pasted boundary. -/
def boundedAboveFlatAffineSectionBassSourceLegEvaluationConeBoundary :=
  (boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare R).toBoundary

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationSourceLeg.lean:33-69"
  "adaptation" "Original positive source-leg movement and independent raw cone-cylinder square"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSourceLegEvaluationConeSquare
