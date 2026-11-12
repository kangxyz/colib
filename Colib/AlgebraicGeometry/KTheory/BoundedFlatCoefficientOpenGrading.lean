/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientPerfectEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenSections
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenDeficitGrading
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectOriginalRestriction
public import Colib.CategoryTheory.Waldhausen.Cofinality.ComplementMap
/-! # Actual ordinary coefficient quotient grading at each coefficient

The same native section category, cofibrations and zero are retained.
Only the original quotient-grade weak class changes. Coefficient naturality,
seed contraction and stable restriction are separate subsequent work.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
/-- The unchanged raw-perfect image quotient for the actual native open inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:51"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
abbrev BoundedAboveFlatCoefficientOpenImageQuotient (a : Under R) :=
  ImageQuotient (perfectOpenWeakWaldhausen (schemeMap f a))
    (perfectComplexesRestrictOpenImmersion (schemeMap f a)) (perfectOpenRestrict_isExact
      (schemeMap f a))

omit [IsOpenImmersion f.left] in
/-- The displayed original perfect evaluation is genuinely exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:57"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
theorem boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).weq
      (RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace).weq
      (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a) :=
  (boundedAboveFlatCoefficientOriginalEvaluation_exact (op P, a)).comp
    (RingedSpace.boundedAboveFlatPerfectInclusion_isExact (space (op P, a)).toRingedSpace)

/-- Actual section grades in the unchanged original geometric image quotient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:67"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
def boundedAboveFlatCoefficientFullOpenGrading (a : Under R) :
    Cofinality.Grading (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
      (BoundedAboveFlatCoefficientOpenImageQuotient f a) :=
  (perfectOpenDeficitGrading (schemeMap f a)).comap
    (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a)

/-- Every section grade is precisely its original perfect evaluation's quotient class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:74"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
theorem boundedAboveFlatCoefficientFullOpenGrading_value (a : Under R)
    (S : BoundedAboveFlatCoefficientSections (op P, a)) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).value S =
      (perfectOpenDeficitGrading (schemeMap f a)).value
        ((boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a).obj S) := rfl

/-- Grade weakness retains the one original joint zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:81"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
theorem boundedAboveFlatCoefficientFullOpenGrading_zero (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.zero =
      boundedAboveFlatCoefficientSectionZero (op P, a) := rfl

/-- The universal algebraic extension is the same raw quotient after actual perfect evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:86"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
theorem boundedAboveFlatCoefficientFullOpenGrading_lift (a : Under R) :
    lift (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
        (boundedAboveFlatCoefficientFullOpenGrading f a) =
      (QuotientAddGroup.mk'
        (CategoryTheory.Waldhausen.AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap
          f a))
          (perfectComplexesRestrictOpenImmersion (schemeMap f a))
          (perfectOpenRestrict_isExact (schemeMap f a))).range).comp
        (CategoryTheory.Waldhausen.AlgebraicGrothendieck.map
          (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
          (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a)
          (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a)) := by
  apply CategoryTheory.Waldhausen.AlgebraicGrothendieck.hom_ext
    (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
  intro S
  rw [lift_objectClass, AddMonoidHom.comp_apply, map_objectClass]
  rfl

/-- The actual restricted section has zero grade by its original geometric image witness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:102"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
theorem boundedAboveFlatCoefficientOpenRestriction_grade_zero (a : Under R)
    (S : BoundedAboveFlatCoefficientSections (op Q, a)) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).value
      ((boundedAboveFlatCoefficientOpenRestriction f a).obj S) = 0 := by
  change (perfectOpenDeficitGrading (schemeMap f a)).value
    ((RingedSpace.boundedAboveFlatPerfectInclusion (space (op P, a)).toRingedSpace).obj
      ((boundedAboveFlatCoefficientOriginalEvaluation (op P, a)).obj
        ((boundedAboveFlatCoefficientOpenRestriction f a).obj S))) = 0
  apply imageQuotientGrading_zero_of_weakImage
  let e := (boundedAboveFlatPerfectOriginalRestrictionIso (schemeMap f a)).app
    ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S) ≪≫
    ((RingedSpace.boundedAboveFlatPerfectInclusion (space (op P, a)).toRingedSpace).mapIso
      ((boundedAboveFlatCoefficientOpenRestrictionEvaluationIso f a).app S)).symm
  refine ⟨(RingedSpace.boundedAboveFlatPerfectInclusion (space (op Q, a)).toRingedSpace).obj
    ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S), e.hom, ?_⟩
  exact (RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace).weq_iso e.hom
    (show IsIso e.hom from inferInstance)

/-- The actual graded Model keeps the native section category, cofibrations and joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:121"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
def boundedAboveFlatCoefficientGradedOpenModel (a : Under R) : WideSubcategory preservesZero.{u+1}
  :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSections (op P, a),
     waldhausen := (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure }⟩

/-- The identity on native sections changes only the actual original weakness class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenGrading.lean:126"
  "adaptation" "Original actual ordinary coefficient raw-image grading"]
def boundedAboveFlatCoefficientOpenGradingModelMap (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenModelFunctor f).obj a ⟶
      boundedAboveFlatCoefficientGradedOpenModel f a :=
  ⟨⟨𝟭 (BoundedAboveFlatCoefficientSections (op P, a)),
    Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f a).nested⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules
