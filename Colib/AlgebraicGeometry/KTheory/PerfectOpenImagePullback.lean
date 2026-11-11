/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectGrothendieckPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenGrothendieckImage

/-!
# Arbitrary quasi-compact open-square action on the original image quotient

The original derived pullback square acts on the fine restriction images.
The proved equality of fine and relative-open images then gives a literal
quotient descent into the unchanged relative-open image quotient. No exact
raw pullback functor or flatness hypothesis is substituted.
-/
@[expose] public section

open AlgebraicGeometry.RingedSpace

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X U' X' : Scheme.{u}} [hU : CompactSpace U] [hX : CompactSpace X]
  [hX' : CompactSpace X']
  (j : U ⟶ X) (j' : U' ⟶ X') [IsOpenImmersion j] [IsOpenImmersion j']
  (p : X' ⟶ X) (q : U' ⟶ U) (h : q ≫ j = j' ≫ p)

include h in
/-- The original derived group maps commute with the unchanged fine restriction maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenImagePullback.lean:35"
  "adaptation" "Original actual ordinary raw-image quotient action"]
theorem perfectGrothendieckPullback_restrictionSquare :
    (perfectGrothendieckPullback q).comp
      (map (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesRestrictOpenImmersion j)
        (perfectComplexesRestrictOpenImmersion_isExact j)) =
    (map (perfectComplexesWaldhausen X'.toRingedSpace) (perfectComplexesRestrictOpenImmersion j')
      (perfectComplexesRestrictOpenImmersion_isExact j')).comp
      (perfectGrothendieckPullback p) := by
  rw [← perfectGrothendieckPullback_restrict j, ← perfectGrothendieckPullback_restrict j',
    ← perfectGrothendieckPullback_comp, ← perfectGrothendieckPullback_comp, h]

include hX hX' h in
/-- The actual coarse-source image is preserved, via its proved equality with the fine image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenImagePullback.lean:45"
  "adaptation" "Original actual ordinary raw-image quotient action"]
theorem perfectOpenImagePullback_range_le :
    (map (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
      (perfectOpenRestrict_isExact j)).range ≤
    (map (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).range.comap (perfectGrothendieckPullback q) := by
  intro x hx
  rw [range_perfectOpenGrothendieckRestrict j] at hx
  change perfectGrothendieckPullback q x ∈
    (map (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).range
  rw [range_perfectOpenGrothendieckRestrict j']
  obtain ⟨a, rfl⟩ := hx
  exact ⟨perfectGrothendieckPullback p a,
    (DFunLike.congr_fun (perfectGrothendieckPullback_restrictionSquare j j' p q h) a).symm⟩

/-- The coefficient map descends directly to the unchanged original relative-open quotient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenImagePullback.lean:61"
  "adaptation" "Original actual ordinary raw-image quotient action"]
def perfectOpenImageQuotientPullback :
    ImageQuotient (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j) →+
    ImageQuotient (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
        (perfectOpenRestrict_isExact j') :=
  QuotientAddGroup.map
    (map (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
      (perfectOpenRestrict_isExact j)).range
    (map (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).range
    (perfectGrothendieckPullback q) (perfectOpenImagePullback_range_le j j' p q h)

/-- Every original target quotient class is sent by the literal original derived group map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenImagePullback.lean:74"
  "adaptation" "Original actual ordinary raw-image quotient action"]
theorem perfectOpenImageQuotientPullback_mk (x : Group (perfectComplexesWaldhausen
  U.toRingedSpace)) :
    perfectOpenImageQuotientPullback j j' p q h
      (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j)
        (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j)).range x) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j')
      (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).range (perfectGrothendieckPullback q x) := rfl

/-- Original bounded-flat classes retain the actual geometric pullback representative. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenImagePullback.lean:82"
  "adaptation" "Original actual ordinary raw-image quotient action"]
theorem perfectOpenImageQuotientPullback_boundedFlat_objectClass (K :
  (boundedAboveFlatPerfectComplex U.toRingedSpace).FullSubcategory) :
    perfectOpenImageQuotientPullback j j' p q h
      ((imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j)).value ((boundedAboveFlatPerfectInclusion
          U.toRingedSpace).obj K)) =
    (imageQuotientGrading (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).value
        ((boundedAboveFlatPerfectInclusion U'.toRingedSpace).obj ((boundedAboveFlatPerfectPullback
          q).obj K)) := by
  change perfectOpenImageQuotientPullback j j' p q h
    (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j)
      (perfectComplexesRestrictOpenImmersion j)
      (perfectOpenRestrict_isExact j)).range
        (objectClass (perfectComplexesWaldhausen U.toRingedSpace)
          ((boundedAboveFlatPerfectInclusion U.toRingedSpace).obj K))) = _
  rw [perfectOpenImageQuotientPullback_mk, perfectGrothendieckPullback_boundedFlat_objectClass]
  rfl

end AlgebraicGeometry.Scheme.Modules
