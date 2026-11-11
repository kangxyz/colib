module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedKValue

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
variable {R : CommRingCat.{u}}

example (i : Index R) :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (boundedAboveFlatCoefficientSectionWaldhausen i)) :=
  boundedAboveFlatCoefficientSectionJointData i

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

example (a : Under R) (n : ℕ) :
    Subsingleton ((boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) :=
  boundedAboveFlatCoefficientGradedOpen_K_succ_subsingleton f a n

example (a : Under R) :
    (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K 0 →*
      Multiplicative (BoundedAboveFlatCoefficientOpenImageQuotient f a) :=
  boundedAboveFlatCoefficientOpenKZeroValueMap f a

example (a : Under R) :
    Function.Injective (boundedAboveFlatCoefficientOpenKZeroValueMap f a) :=
  boundedAboveFlatCoefficientOpenKZeroValueMap_injective f a

