/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterRegular
public import Colib.AlgebraicGeometry.Products.Diagonal.ParameterBaseChange

/-!
# The actual remaining diagonal after the ambient parameter quotient

SOURCE ONLY, UNCOMPILED. The remaining `Y` diagonal cuts out the actual exterior
triple product, not a replacement scheme. Its projection to `Y ×[k] Y` is flat
because the independent outside factors and parameter are smooth. This uses no
flatness of a correspondence support over `X` or `Y`.

The generic product-diagonal factorization is applied to the literal middle-pair
map. The equality with the frozen direct remaining-pair construction is proved
on both coordinates. All original smooth schemes may be empty or disconnected.
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
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f g h

/-- The frozen remaining pair is the generic diagonal factorization's actual map. -/
theorem exteriorAmbientRemainingPair_eq :
    exteriorAmbientRemainingPair X Y Z T =
      ProductDiagonalBaseChange.remainingMap Y.hom T.hom m := by
  have hι : exteriorAmbientParameterInclusion X Y Z T =
      ProductDiagonalBaseChange.quotientInclusion Y.hom T.hom m := rfl
  apply pullback.hom_ext
  · rw [exteriorAmbientRemainingPair_fst, ProductDiagonalBaseChange.remainingMap_fst, hι]
    simp [correspondenceMiddlePair, pullback.map, Category.assoc]
  · rw [exteriorAmbientRemainingPair_snd, ProductDiagonalBaseChange.remainingMap_snd, hι]
    simp [correspondenceMiddlePair, pullback.map, Category.assoc]

/-- This is ambient flatness, not flatness on the coefficient supports. -/
instance exteriorAmbientRemainingPair_flat : Flat (exteriorAmbientRemainingPair X Y Z T) := by
  rw [exteriorAmbientRemainingPair_eq]
  infer_instance

/-- The actual exterior triple inclusion factored through the actual parameter quotient. -/
def exteriorAmbientRemainingInclusion : correspondenceTripleProduct f g h ⟶
    exteriorAmbientParameterQuotient X Y Z T :=
  ProductDiagonalBaseChange.diagonalLift Y.hom T.hom m
    (correspondenceTripleMiddle f g h) (correspondenceTripleInclusion f g h)
    (correspondenceTriple_isPullback f g h)

@[reassoc (attr := simp)]
theorem exteriorAmbientRemainingInclusion_parameterInclusion :
    exteriorAmbientRemainingInclusion X Y Z T ≫ exteriorAmbientParameterInclusion X Y Z T =
      correspondenceTripleInclusion f g h :=
  ProductDiagonalBaseChange.diagonalLift_quotientInclusion _ _ _ _ _ _

/-- Imposing the remaining Y equations recovers the full, unreduced exterior triple product. -/
theorem exteriorAmbientRemaining_isPullback :
    IsPullback (correspondenceTripleMiddle f g h ≫ pullback.fst Y.hom T.hom)
      (exteriorAmbientRemainingInclusion X Y Z T)
      (pullback.diagonal Y.hom) (exteriorAmbientRemainingPair X Y Z T) := by
  rw [exteriorAmbientRemainingPair_eq]
  exact ProductDiagonalBaseChange.diagonalLift_isPullback _ _ _ _ _ _

instance exteriorAmbientRemainingInclusion_isClosedImmersion :
    IsClosedImmersion (exteriorAmbientRemainingInclusion X Y Z T) :=
  MorphismProperty.of_isPullback (exteriorAmbientRemaining_isPullback X Y Z T) inferInstance

/-- The remaining ideal is the full inverse image of the original diagonal ideal. -/
theorem exteriorAmbientRemainingInclusion_ker :
    (exteriorAmbientRemainingInclusion X Y Z T).ker =
      (pullback.diagonal Y.hom).ker.comap (exteriorAmbientRemainingPair X Y Z T) := by
  let sq := (exteriorAmbientRemaining_isPullback X Y Z T).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Products/Diagonal/ExteriorIdentity.lean:78-111"
  "adaptation" "Flat remaining ambient pair and the actual exterior triple product as \
  the Cartesian inverse image of the original Y diagonal after the parameter quotient"]
  exteriorAmbientRemainingPair_flat exteriorAmbientRemainingInclusion
  exteriorAmbientRemainingInclusion_parameterInclusion exteriorAmbientRemaining_isPullback
  exteriorAmbientRemainingInclusion_ker

end Stacks.Chow
