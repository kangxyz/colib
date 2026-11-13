/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedReindex
public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull


/-!
# The canonical supported native coefficient localization null

The actual supported restriction has zero grade in its original supported
image quotient. Unique arrows from the same supported joint zero are therefore
weak in G_Z. Reversing their original realization gives the whole null of the
original r_Z followed by q_Z, with the same null time for every coefficient
arrow. The coefficient diagrams require compact P and Q; no quasi-separated
or auxiliary-complement compactness premise is used to construct this null.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Unique arrows from the inherited supported joint zero to actual supported restrictions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenNull.lean:30"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedOpenZeroToGraded (a : Under R) :
    (Functor.const (BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a)).obj
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).zero ⟶
      boundedAboveFlatCoefficientSupportedOpenRestriction f T a where
  app _ := (boundedAboveFlatCoefficientSupportedSectionWaldhausen
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).isZero.to_ _
  naturality _ _ _ := (boundedAboveFlatCoefficientSupportedSectionWaldhausen
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).isZero.eq_of_src _ _

/-- These actual zero-to-image arrows are weak by the original supported restriction witness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenNull.lean:41"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenZeroToGraded_weak (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientSupportedOpenZeroToGraded f T a).app S) :=
  (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).zero.trans
    (boundedAboveFlatCoefficientSupportedOpenRestriction_grade_zero f T a S).symm

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Reversed zero-to-image realization constructs the original coefficient-natural supported null.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenNull.lean:52"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull :
    LoopPrespectrum.DiagramNullHomotopy
      (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
      (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T) :=
  modelDiagramZeroNull (boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (fun a ↦ boundedAboveFlatCoefficientSupportedOpenZeroToGraded f T a)
    (fun a ↦ boundedAboveFlatCoefficientSupportedOpenZeroToGraded_weak f T a)

/-- Every original coefficient arrow preserves the whole supported localization-null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenNull.lean:62"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull_coefficient
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
        (((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s,
          x)) =
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy b).level n
        (s, ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).map g).map n x) :=
  (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality g n s x

end AlgebraicGeometry.Scheme.Modules

