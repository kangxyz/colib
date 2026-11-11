/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedPerfectEvaluation
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedOriginalRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenImageGrading
public import Colib.CategoryTheory.Waldhausen.Cofinality.ComplementMap




/-! # Pointwise native supported coefficient grading

The original supported evaluation gives the actual raw image-quotient grade. Restriction has
zero grade by its original geometric image witness. The graded Model retains the same category,
cofibrations and chosen joint zero. These pointwise definitions require no compactness.
Coefficient-natural graded reindexing, seed contraction and G7 comparison are separate owners.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation

/-- The actual raw supported image quotient for the same native support and localization opens. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:50"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
abbrev BoundedAboveFlatCoefficientSupportedOpenImageQuotient (a : Under R) :=
  PerfectSupportedOpenImageQuotient (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)

omit [IsOpenImmersion f.left] in
/-- The original supported perfect evaluation is exact for the actual fine structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:55"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact (a : Under R) :
    IsExact
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq
      (perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).cof
      (perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a) :=
  (boundedAboveFlatCoefficientSupportedEvaluation_exact
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).comp
    (boundedAboveFlatPerfectSupportedInclusion_isExact (boundedAboveFlatCoefficientOpenSupportOpen
      f T a).ι)

/-- Original supported native open sections carry their actual raw image-quotient grades. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:69"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def boundedAboveFlatCoefficientSupportedFullOpenGrading (a : Under R) :
    Cofinality.Grading
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
      (BoundedAboveFlatCoefficientSupportedOpenImageQuotient f T a) :=
  (perfectSupportedOpenDeficitGrading
    (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).comap
    (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)

/-- Native grades retain the actual original supported perfect evaluation value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:79"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem boundedAboveFlatCoefficientSupportedFullOpenGrading_value (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value S =
      (perfectSupportedOpenDeficitGrading (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).value
        ((boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj S) := rfl

/-- The graded structure retains the restriction of the same original joint global zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:87"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem boundedAboveFlatCoefficientSupportedFullOpenGrading_zero (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.zero =
      boundedAboveFlatCoefficientSupportedSectionZero
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι := rfl

/-- The actual native algebraic grading extension is the unchanged raw quotient projection. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:93"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem boundedAboveFlatCoefficientSupportedFullOpenGrading_lift (a : Under R) :
    lift (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
        (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a) =
      (QuotientAddGroup.mk'
        (map (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedOpenRestrict_waldhausenExact
            (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a))).range).comp
        (map (boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
          (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
          (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)) := by
  apply CategoryTheory.Waldhausen.AlgebraicGrothendieck.hom_ext
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
  intro S
  rw [lift_objectClass, AddMonoidHom.comp_apply, map_objectClass]
  rfl

/-- Actual supported native restriction has zero quotient grade by its original image witness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:114"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_grade_zero (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value
      ((boundedAboveFlatCoefficientSupportedOpenRestriction f T a).obj S) = 0 := by
  change (perfectSupportedOpenDeficitGrading (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a)).value
      ((boundedAboveFlatPerfectSupportedInclusion
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).obj
        ((boundedAboveFlatCoefficientSupportedEvaluation
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).obj
          ((boundedAboveFlatCoefficientSupportedOpenRestriction f T a).obj S))) = 0
  apply imageQuotientGrading_zero_of_weakImage
  let e := (boundedAboveFlatPerfectSupportedOriginalRestrictionIso (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a)).app
      ((boundedAboveFlatCoefficientSupportedEvaluation
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj S)
    ≪≫ ((boundedAboveFlatPerfectSupportedInclusion
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).mapIso
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionEvaluationIso f T a).app S)).symm
  refine ⟨(boundedAboveFlatPerfectSupportedInclusion
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj
    ((boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
      a).ι).obj S),
    e.hom, ?_⟩
  exact (perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).weq_iso
    e.hom
    (show IsIso e.hom from inferInstance)

/-- The actual graded supported native Model retains its category, cofibrations, and joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:141"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def boundedAboveFlatCoefficientSupportedGradedOpenModel (a : Under R) : WideSubcategory
  preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSupportedOpenSections f T a,
       waldhausen := (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure }⟩

/-- The original identity on supported native sections changes only quotient-grade weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenGrading.lean:146"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def boundedAboveFlatCoefficientSupportedOpenGradingModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenModel f T a :=
  ⟨⟨𝟭 (BoundedAboveFlatCoefficientSupportedOpenSections f T a),
      Fibration.changeWeak_exact (boundedAboveFlatCoefficientSupportedFullOpenGrading f T
        a).nested⟩,
    rfl⟩

end AlgebraicGeometry.Scheme.Modules
