/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenGradingNaturality
public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull

/-!
# The canonical global coefficient-open localization null

The original restriction-image witness gives zero quotient grade to every actual restricted
native section. The unique arrows from the same joint section zero are therefore weak in
the actual graded Model. Reversing their original realized tracks constructs the whole null
of the original r followed by q, naturally at the same time for every coefficient arrow.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Unique arrows from the inherited joint zero to the actual native restricted sections. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenNull.lean:28"
  "adaptation" "Original ordinary whole coefficient-natural localization null"]
def boundedAboveFlatCoefficientOpenZeroToGraded (a : Under R) :
    (Functor.const (BoundedAboveFlatCoefficientSections (Opposite.op Q, a))).obj
        (boundedAboveFlatCoefficientSectionWaldhausen (Opposite.op P, a)).zero ⟶
      boundedAboveFlatCoefficientOpenRestriction f a where
  app _ := (boundedAboveFlatCoefficientSectionWaldhausen (Opposite.op P, a)).isZero.to_ _
  naturality _ _ _ :=
    (boundedAboveFlatCoefficientSectionWaldhausen (Opposite.op P, a)).isZero.eq_of_src _ _

/-- These original zero-to-image arrows are weak by the constructed restriction-image witness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenNull.lean:37"
  "adaptation" "Original ordinary whole coefficient-natural localization null"]
theorem boundedAboveFlatCoefficientOpenZeroToGraded_weak (a : Under R)
    (S : BoundedAboveFlatCoefficientSections (Opposite.op Q, a)) :
    (boundedAboveFlatCoefficientGradedOpenModel f a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientOpenZeroToGraded f a).app S) :=
  (boundedAboveFlatCoefficientFullOpenGrading f a).zero.trans
    (boundedAboveFlatCoefficientOpenRestriction_grade_zero f a S).symm

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The reversed zero-to-image realization gives the canonical whole coefficient-natural null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenNull.lean:47"
  "adaptation" "Original ordinary whole coefficient-natural localization null"]
def boundedAboveFlatCoefficientOpenGradingDiagramNull :
    LoopPrespectrum.DiagramNullHomotopy
      (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
      (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f) :=
  modelDiagramZeroNull (boundedAboveFlatCoefficientOpenRestrictionModelTransformation f)
    (boundedAboveFlatCoefficientOpenGradingModelTransformation f)
    (fun a ↦ boundedAboveFlatCoefficientOpenZeroToGraded f a)
    (fun a ↦ boundedAboveFlatCoefficientOpenZeroToGraded_weak f a)

/-- Every native coefficient arrow keeps the complete original localization-null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenNull.lean:57"
  "adaptation" "Original ordinary whole coefficient-natural localization null"]
theorem boundedAboveFlatCoefficientOpenGradingDiagramNull_coefficient
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) =
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy b).level n
        (s, ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).map g).map n x) :=
  (boundedAboveFlatCoefficientOpenGradingDiagramNull f).naturality g n s x

end AlgebraicGeometry.Scheme.Modules
