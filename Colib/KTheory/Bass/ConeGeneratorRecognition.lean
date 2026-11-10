/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.StrictSquareMapHomotopy

/-! Generator characterization of the represented action on an actual square cone. -/
@[expose] public noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare.MapHomotopy
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} {a b : S ⟶ T}

/-- The literal outer cone cylinder, with its original span point and height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeGeneratorRecognition.lean:18-23"
  "adaptation" "Original whole maps and independent time coordinates retained"]
abbrev coneCylinder (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)
    (s : unitInterval) (z : (StrictSquare.span S).space n) :=
  ReducedMappingCone.cylinder ((StrictSquare.span S).point n) (S.right.right.point n)
    ((StrictSquare.comparison S).map n) (s, z)

/-- Four generator values specify the inherited action without mentioning its descended map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeGeneratorRecognition.lean:24-47"
  "adaptation" "Original whole maps and independent time coordinates retained"]
structure ConeGeneratorLaw (H : MapHomotopy a b)
    (K : Homotopy (mappingConeMap (strictSquareComparisonFunctor.map a))
      (mappingConeMap (strictSquareComparisonFunctor.map b))) : Prop where
  /-- The Laurent input receives exactly the independent final-corner action. -/
  laurent : ∀ n r y,
    K.level n (r, (mappingConeInclusion (StrictSquare.comparison S)).map n y) =
      (mappingConeInclusion (StrictSquare.comparison T)).map n (H.target.level n (r, y))
  /-- The positive chart retains the original outer height. -/
  upper : ∀ n r s y,
    K.level n (r, coneCylinder S n s ((HomotopyPushout.inl S.left.hom S.hom.left).map n y)) =
      coneCylinder T n s ((HomotopyPushout.inl T.left.hom T.hom.left).map n
        (H.upper.level n (r, y)))
  /-- The negative chart retains the original outer height. -/
  lower : ∀ n r s y,
    K.level n (r, coneCylinder S n s ((HomotopyPushout.inr S.left.hom S.hom.left).map n y)) =
      coneCylinder T n s ((HomotopyPushout.inr T.left.hom T.hom.left).map n
        (H.lower.level n (r, y)))
  /-- Both old quotient heights remain independent of the coefficient-action time. -/
  overlap : ∀ n r s q x,
    K.level n (r, coneCylinder S n s (HomotopyPushout.cylinder S.left.hom S.hom.left n (q, x))) =
      coneCylinder T n s (HomotopyPushout.cylinder T.left.hom T.hom.left n
        (q, H.source.level n (r, x)))

/-- The actual descended cone action satisfies each of the independent corner formulas. -/
@[colib_tag "COL-0514", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeGeneratorRecognition.lean:48-54"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem cone_generatorLaw (H : MapHomotopy a b) : ConeGeneratorLaw H H.cone where
  laurent := by intros; rfl
  upper := by intros; rfl
  lower := by intros; rfl
  overlap := by intros; rfl

/-- The quotient generators determine the entire continuous based action uniquely. -/
@[colib_tag "COL-0514", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeGeneratorRecognition.lean:55-78"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem eq_cone_of_generatorLaw (H : MapHomotopy a b)
    (K : Homotopy (mappingConeMap (strictSquareComparisonFunctor.map a))
      (mappingConeMap (strictSquareComparisonFunctor.map b)))
    (h : ConeGeneratorLaw H K) : K = H.cone := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r, z⟩
  induction z using Quot.inductionOn with
  | h z =>
    cases z with
    | inl y => exact h.laurent n r y
    | inr z =>
      obtain ⟨s, z⟩ := z
      induction z using Quot.inductionOn with
      | h z =>
        cases z with
        | inl z =>
          cases z with
          | inl y => exact h.upper n r s y
          | inr y => exact h.lower n r s y
        | inr z => exact h.overlap n r s z.1 z.2

end Topology.LoopPrespectrum.StrictSquare.MapHomotopy
