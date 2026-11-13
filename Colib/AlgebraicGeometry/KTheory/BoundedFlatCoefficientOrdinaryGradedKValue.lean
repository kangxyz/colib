/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenGrading
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.EquivalenceJoint
public import Colib.KTheory.Waldhausen.Cofinality.GeneralKZeroValue

/-! # Original ordinary graded K-value

The original four lower declarations retain actual joint cylinders transported along the
ordinary coefficient evaluation equivalence, positive graded K-vanishing and the injective
K-zero value map. They do not assert cofinality, exactness or initial cone stability.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- Actual bounded-flat joint cylinders transport along the original native evaluation inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:112"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
def boundedAboveFlatCoefficientSectionJointData (i : Index R) :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (boundedAboveFlatCoefficientSectionWaldhausen i)) :=
  Fibration.RowFactorization.JointData.ofExactEquivalence
    (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)
      (boundedAboveFlatCoefficientSectionWaldhausen i)
    (boundedAboveFlatCoefficientSectionEquivalence i).symm
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact i)
    (boundedAboveFlatCoefficientOriginalEvaluation_exact i)
      (RingedSpace.boundedAboveFlatPerfectJointData (space i).toRingedSpace
      (Fibration.NestedWeakEquivalences.refl _))

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- The original graded section target has zero positive K-groups by its actual fine joint data. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:125"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientGradedOpen_K_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton ((boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) :=
  (boundedAboveFlatCoefficientFullOpenGrading f a).coarse_K_succ_subsingleton_general
    (boundedAboveFlatCoefficientSectionJointData (op P, a)) n

/-- Original coarse K-zero values land in the unchanged actual raw-perfect image quotient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:131"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
def boundedAboveFlatCoefficientOpenKZeroValueMap (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K 0 →*
      Multiplicative (BoundedAboveFlatCoefficientOpenImageQuotient f a) :=
  (boundedAboveFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap
    (boundedAboveFlatCoefficientSectionJointData (op P, a)).reflexiveAsSmall.sourceFactorization

/-- The original value map detects equality of the actual graded section K-zero classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:138"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientOpenKZeroValueMap_injective (a : Under R) :
    Function.Injective (boundedAboveFlatCoefficientOpenKZeroValueMap f a) :=
  (boundedAboveFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap_injective
    (boundedAboveFlatCoefficientSectionJointData (op P, a)).reflexiveAsSmall.sourceFactorization

end AlgebraicGeometry.Scheme.Modules
