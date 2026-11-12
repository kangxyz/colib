module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenGrading
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.zero =
      boundedAboveFlatCoefficientSectionZero (op P, a) :=
  boundedAboveFlatCoefficientFullOpenGrading_zero f a
example (a : Under R) (S : BoundedAboveFlatCoefficientSections (op Q, a)) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).value
      ((boundedAboveFlatCoefficientOpenRestriction f a).obj S) = 0 :=
  boundedAboveFlatCoefficientOpenRestriction_grade_zero f a S
example (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenModelFunctor f).obj a ⟶
      boundedAboveFlatCoefficientGradedOpenModel f a :=
  boundedAboveFlatCoefficientOpenGradingModelMap f a
