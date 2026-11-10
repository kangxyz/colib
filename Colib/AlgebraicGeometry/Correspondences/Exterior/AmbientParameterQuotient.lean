/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleDiagonal
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# The parameter quotient of the actual exterior ambient

The existing four-factor correspondence ambient has two middle coordinates in
`Y ×[k] T`. Project them to `T ×[k] T` and take the literal inverse image of
the parameter diagonal. The quotient retains the full scheme structure and
the two original `Y` coordinates. No remaining middle equation is imposed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Z T).hom

/-- The two actual middle parameter coordinates of the exterior ambient. -/
def exteriorAmbientParameterPair :
    correspondenceIntersectionAmbient f g h ⟶ pullback T.hom T.hom :=
  correspondenceMiddlePair f g h ≫
    pullback.map g g T.hom T.hom (pullback.snd Y.hom T.hom)
      (pullback.snd Y.hom T.hom) (𝟙 (Spec (.of k)))
      ((Category.comp_id _).trans pullback.condition)
      ((Category.comp_id _).trans pullback.condition)

@[reassoc (attr := simp)]
theorem exteriorAmbientParameterPair_fst :
    exteriorAmbientParameterPair X Y Z T ≫ pullback.fst T.hom T.hom =
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
        pullback.snd f g ≫ pullback.snd Y.hom T.hom := by
  simp [exteriorAmbientParameterPair, correspondenceMiddlePair, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem exteriorAmbientParameterPair_snd :
    exteriorAmbientParameterPair X Y Z T ≫ pullback.snd T.hom T.hom =
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
        pullback.fst g h ≫ pullback.snd Y.hom T.hom := by
  simp [exteriorAmbientParameterPair, correspondenceMiddlePair, pullback.map, Category.assoc]

/-- The original middle pair before imposing any diagonal equation. -/
def exteriorAmbientOldMiddlePair :
    correspondenceIntersectionAmbient f g h ⟶ pullback Y.hom Y.hom :=
  correspondenceMiddlePair f g h ≫
    pullback.map g g Y.hom Y.hom (pullback.fst Y.hom T.hom)
      (pullback.fst Y.hom T.hom) (𝟙 (Spec (.of k))) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem exteriorAmbientOldMiddlePair_fst :
    exteriorAmbientOldMiddlePair X Y Z T ≫ pullback.fst Y.hom Y.hom =
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
        pullback.snd f g ≫ pullback.fst Y.hom T.hom := by
  simp [exteriorAmbientOldMiddlePair, correspondenceMiddlePair, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem exteriorAmbientOldMiddlePair_snd :
    exteriorAmbientOldMiddlePair X Y Z T ≫ pullback.snd Y.hom Y.hom =
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
        pullback.fst g h ≫ pullback.fst Y.hom T.hom := by
  simp [exteriorAmbientOldMiddlePair, correspondenceMiddlePair, pullback.map, Category.assoc]

/-- Impose only equality of the two actual middle parameter coordinates. -/
abbrev exteriorAmbientParameterQuotient : Scheme.{u} :=
  pullback (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T)

/-- The full scheme-theoretic parameter-diagonal inclusion in the exterior ambient. -/
abbrev exteriorAmbientParameterInclusion : exteriorAmbientParameterQuotient X Y Z T ⟶
    correspondenceIntersectionAmbient f g h :=
  pullback.snd (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T)

instance exteriorAmbientParameterInclusion_isClosedImmersion :
    IsClosedImmersion (exteriorAmbientParameterInclusion X Y Z T) := inferInstance

/-- The literal Cartesian square defining the ambient parameter quotient. -/
theorem exteriorAmbientParameter_isPullback :
    IsPullback
      (pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T))
      (exteriorAmbientParameterInclusion X Y Z T)
      (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T) :=
  IsPullback.of_hasPullback _ _

/-- The two original middle coordinates remain after imposing the parameter diagonal. -/
def exteriorAmbientRemainingPair :
    exteriorAmbientParameterQuotient X Y Z T ⟶ pullback Y.hom Y.hom :=
  exteriorAmbientParameterInclusion X Y Z T ≫ exteriorAmbientOldMiddlePair X Y Z T

@[reassoc (attr := simp)]
theorem exteriorAmbientRemainingPair_fst :
    exteriorAmbientRemainingPair X Y Z T ≫ pullback.fst Y.hom Y.hom =
      exteriorAmbientParameterInclusion X Y Z T ≫
        pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
          pullback.snd f g ≫ pullback.fst Y.hom T.hom := by
  simp [exteriorAmbientRemainingPair]

@[reassoc (attr := simp)]
theorem exteriorAmbientRemainingPair_snd :
    exteriorAmbientRemainingPair X Y Z T ≫ pullback.snd Y.hom Y.hom =
      exteriorAmbientParameterInclusion X Y Z T ≫
        pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
          pullback.fst g h ≫ pullback.fst Y.hom T.hom := by
  simp [exteriorAmbientRemainingPair]

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Products/Diagonal/ExteriorIdentity.lean:39-55,61-76"
  "adaptation" "Literal ambient parameter-diagonal quotient and both original middle \
  coordinates, using the native four-factor ambient and pullback maps"]
  exteriorAmbientParameterPair exteriorAmbientOldMiddlePair exteriorAmbientParameterQuotient
  exteriorAmbientParameterInclusion exteriorAmbientParameter_isPullback
  exteriorAmbientRemainingPair exteriorAmbientRemainingPair_fst exteriorAmbientRemainingPair_snd

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Products/Diagonal/BaseChange.lean:88-90,96-108"
  "adaptation" "The remaining pair is characterized by both original middle projections; \
  the construction here uses the equivalent direct native pullback map"]
  exteriorAmbientRemainingPair exteriorAmbientRemainingPair_fst exteriorAmbientRemainingPair_snd

end Stacks.Chow
