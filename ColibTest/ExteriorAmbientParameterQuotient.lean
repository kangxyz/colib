module

import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterQuotient

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme

noncomputable section
universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))

example : IsClosedImmersion (exteriorAmbientParameterInclusion X Y Z T) := inferInstance

example : IsPullback
    (pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T))
    (exteriorAmbientParameterInclusion X Y Z T)
    (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T) :=
  exteriorAmbientParameter_isPullback X Y Z T

/-- Every actual ambient point-family with equal parameters has the required lift. -/
example {W : Scheme.{u}}
    (a : W ⟶ correspondenceIntersectionAmbient (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    (t : W ⟶ T.left)
    (ht : t ≫ pullback.diagonal T.hom = a ≫ exteriorAmbientParameterPair X Y Z T) :
    ∃ l : W ⟶ exteriorAmbientParameterQuotient X Y Z T,
      l ≫ exteriorAmbientParameterInclusion X Y Z T = a ∧
      l ≫ exteriorAmbientRemainingPair X Y Z T = a ≫ exteriorAmbientOldMiddlePair X Y Z T := by
  refine ⟨pullback.lift t a ht, pullback.lift_snd _ _ _, ?_⟩
  change pullback.lift t a ht ≫ pullback.snd _ _ ≫
    exteriorAmbientOldMiddlePair X Y Z T = a ≫ exteriorAmbientOldMiddlePair X Y Z T
  exact pullback.lift_snd_assoc _ _ _ _

/-- The ambient quotient kernel is the inverse image of the actual parameter-diagonal ideal. -/
example : (exteriorAmbientParameterInclusion X Y Z T).ker =
    (pullback.diagonal T.hom).ker.comap (exteriorAmbientParameterPair X Y Z T) := by
  let sq := (exteriorAmbientParameter_isPullback X Y Z T).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

example : exteriorAmbientRemainingPair X Y Z T ≫ pullback.fst Y.hom Y.hom =
    exteriorAmbientParameterInclusion X Y Z T ≫
      pullback.fst
        (pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          (SmoothSite.product Y T).hom)
        (pullback.fst (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫
          (SmoothSite.product Y T).hom) ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          pullback.fst Y.hom T.hom :=
  exteriorAmbientRemainingPair_fst X Y Z T
