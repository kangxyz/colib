module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenGrading

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    (perfectSupportedOpenDeficitGrading j T).value K = 0 ↔
      objectClass (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) K ∈
        (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
          (perfectSupportedOpenRestrict_waldhausenExact j T)).range :=
  perfectSupportedOpenDeficitGrading_zero_iff j T K

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) :
    boundedAboveFlatPerfectSupportedInclusion T.ι ⋙ perfectSupportedRestrict j T ≅
      boundedAboveFlatPerfectSupportedPullback (Scheme.supportRestrictionPair j T) ⋙
        boundedAboveFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι :=
  boundedAboveFlatPerfectSupportedOriginalRestrictionIso j T

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R) :
    boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a =
      boundedAboveFlatCoefficientSupportedEvaluation
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι ⋙
        boundedAboveFlatPerfectSupportedInclusion
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι := rfl

example (a : Under R) (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value S =
      (perfectSupportedOpenDeficitGrading (Scheme.BaseChange.Coefficients.schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).value
        ((boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj S) :=
  boundedAboveFlatCoefficientSupportedFullOpenGrading_value f T a S

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.zero =
      boundedAboveFlatCoefficientSupportedSectionZero
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι :=
  boundedAboveFlatCoefficientSupportedFullOpenGrading_zero f T a

example (a : Under R) :
    lift (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a) =
      (QuotientAddGroup.mk'
        (map (perfectSupportedOpenWeakWaldhausen (Scheme.BaseChange.Coefficients.schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedRestrict (Scheme.BaseChange.Coefficients.schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedOpenRestrict_waldhausenExact
            (Scheme.BaseChange.Coefficients.schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a))).range).comp
        (map (boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
          (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
          (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)) :=
  boundedAboveFlatCoefficientSupportedFullOpenGrading_lift f T a

example (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value
      ((boundedAboveFlatCoefficientSupportedOpenRestriction f T a).obj S) = 0 :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_grade_zero f T a S

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a).hom.toFunctor =
      𝟭 (BoundedAboveFlatCoefficientSupportedOpenSections f T a) := rfl

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a).obj.waldhausen.zero =
      boundedAboveFlatCoefficientSupportedSectionZero
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι := rfl
