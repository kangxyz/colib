/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Diagonal
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.IntersectionIdeal

/-!
# The two middle diagonals in the actual sixfold ambient

All schemes are literal native pullbacks. The fourfold product is their
Cartesian intersection, and its ideal is the sum of both diagonal ideals.
No smoothness, field, connectedness, or reduction is imposed.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Products/Diagonal/TripleAmbient.lean (blob aa9beffb696437b23e710d439b11aee4628bb888)
and TripleIdeals.lean (blob 83346c82c61d0b6b039f608f618f7fce4c11c3bc).
The actual Cartesian diagonal theorem is Mathlib's
pullback_map_diagonal_isPullback. Regular-sequence and Tor comparisons are
separate obligations; the original regular-list arguments are not imported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The last coordinate of the four-factor ambient scheme. -/
abbrev correspondenceAmbientTarget : correspondenceIntersectionAmbient f g h ⟶ Z :=
  pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.snd g h

/-- The last coordinate after imposing the first middle diagonal. -/
abbrev correspondenceTripleTarget : correspondenceTripleProduct f g h ⟶ Z :=
  pullback.snd (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd g h

/-- The actual product of the three adjacent two-factor ambient schemes. -/
abbrev correspondenceSixfoldAmbient : Scheme.{u} :=
  pullback (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)

/-- The first middle diagonal imposed in the six-factor ambient. -/
abbrev correspondenceFirstDiagonal : Scheme.{u} :=
  pullback (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)

/-- Both middle diagonals imposed, giving the actual fourfold product. -/
abbrev correspondenceFourfoldProduct : Scheme.{u} :=
  pullback (correspondenceTripleTarget f g h) (pullback.fst h i)

/-- The first diagonal inclusion is the exterior product of the original
middle-diagonal inclusion with the identity of the last adjacent product. -/
def correspondenceFirstDiagonalInclusion : correspondenceFirstDiagonal f g h i ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.map _ _ _ _ (correspondenceTripleInclusion f g h) (𝟙 _) (𝟙 S)
    (by simp [correspondenceTripleTarget, correspondenceAmbientTarget]) (by simp)

set_option backward.isDefEq.respectTransparency false in
instance [IsSeparated g] : IsClosedImmersion (correspondenceFirstDiagonalInclusion f g h i) := by
  unfold correspondenceFirstDiagonalInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceTripleInclusion f g h)))
    (inferInstanceAs (IsClosedImmersion (𝟙 (pullback h i)))) (by simp) (by simp)

/-- The second diagonal inclusion identifies the two remaining Z coordinates. -/
abbrev correspondenceSecondDiagonalInclusion : correspondenceFourfoldProduct f g h i ⟶
    correspondenceFirstDiagonal f g h i :=
  pullback.mapDesc (correspondenceTripleTarget f g h) (pullback.fst h i) h

instance [IsSeparated h] : IsClosedImmersion (correspondenceSecondDiagonalInclusion f g h i) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc (correspondenceTripleTarget f g h) (pullback.fst h i) h))

/-- The first diagonal keeps the original triple-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceFirstDiagonalInclusion_fst :
    correspondenceFirstDiagonalInclusion f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
      correspondenceTripleInclusion f g h := pullback.lift_fst _ _ _

/-- The first diagonal keeps the last adjacent-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceFirstDiagonalInclusion_snd :
    correspondenceFirstDiagonalInclusion f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) := by
  simp only [correspondenceFirstDiagonalInclusion, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- The second diagonal keeps the first three coordinates. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalInclusion_fst :
    correspondenceSecondDiagonalInclusion f g h i ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondDiagonalInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second diagonal keeps the last adjacent product. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalInclusion_snd :
    correspondenceSecondDiagonalInclusion f g h i ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondDiagonalInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]




/-- The two middle coordinates of the original four-factor ambient. -/
def correspondenceMiddlePair : correspondenceIntersectionAmbient f g h ⟶ pullback g g :=
  pullback.map _ _ g g (pullback.snd f g) (pullback.fst g h) (𝟙 S)
    (by simp) (by simp)

/-- The original middle coordinate of the actual triple product. -/
abbrev correspondenceTripleMiddle : correspondenceTripleProduct f g h ⟶ Y :=
  pullback.fst _ _ ≫ pullback.snd f g

/-- The original triple product is the actual base change of the middle diagonal. -/
theorem correspondenceTriple_isPullback :
    IsPullback (correspondenceTripleMiddle f g h) (correspondenceTripleInclusion f g h)
      (pullback.diagonal g) (correspondenceMiddlePair f g h) :=
  pullback_map_diagonal_isPullback (pullback.snd f g) (pullback.fst g h) g

/-- The two Y coordinates in the original six-factor ambient. -/
abbrev correspondenceSixfoldFirstMiddlePair : correspondenceSixfoldAmbient f g h i ⟶
    pullback g g :=
  pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
    correspondenceMiddlePair f g h

/-- The first six-factor diagonal is the actual exterior base change of the
original four-factor diagonal. -/
theorem correspondenceFirstDiagonal_baseChange :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) := by
  apply IsPullback.flip
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback
    (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)).flip)
  · simpa [correspondenceAmbientTarget, correspondenceTripleTarget] using
      (IsPullback.of_hasPullback
        (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)).flip
  · exact correspondenceFirstDiagonalInclusion_fst f g h i

/-- The actual first middle diagonal square in the six-factor ambient. -/
theorem correspondenceSixfoldFirstDiagonal_isPullback :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        correspondenceTripleMiddle f g h)
      (correspondenceFirstDiagonalInclusion f g h i)
      (pullback.diagonal g) (correspondenceSixfoldFirstMiddlePair f g h i) :=
  (correspondenceFirstDiagonal_baseChange f g h i).paste_horiz
    (correspondenceTriple_isPullback f g h)

/-- The two Z coordinates in the same original six-factor ambient. -/
def correspondenceSixfoldSecondMiddlePair : correspondenceSixfoldAmbient f g h i ⟶
    pullback h h :=
  pullback.map _ _ h h (correspondenceAmbientTarget f g h) (pullback.fst h i) (𝟙 S)
    (by simp) (by simp)

/-- Imposing only the second middle diagonal in the original ambient. -/
abbrev correspondenceSecondDiagonalAmbient : Scheme.{u} :=
  pullback (correspondenceAmbientTarget f g h) (pullback.fst h i)

/-- The original ambient inclusion imposing only the second middle diagonal. -/
abbrev correspondenceSecondAmbientInclusion : correspondenceSecondDiagonalAmbient f g h i ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.mapDesc (correspondenceAmbientTarget f g h) (pullback.fst h i) h

instance [IsSeparated h] : IsClosedImmersion (correspondenceSecondAmbientInclusion f g h i) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc (correspondenceAmbientTarget f g h) (pullback.fst h i) h))

/-- The second six-factor diagonal is the genuine pullback of the Z diagonal. -/
theorem correspondenceSixfoldSecondDiagonal_isPullback :
    IsPullback
      (pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
        correspondenceAmbientTarget f g h)
      (correspondenceSecondAmbientInclusion f g h i)
      (pullback.diagonal h) (correspondenceSixfoldSecondMiddlePair f g h i) :=
  pullback_map_diagonal_isPullback (correspondenceAmbientTarget f g h) (pullback.fst h i) h

/-- The fourfold product maps to the original second-diagonal source by the
actual first middle-diagonal inclusion. -/
def correspondenceFourfoldToSecondAmbient : correspondenceFourfoldProduct f g h i ⟶
    correspondenceSecondDiagonalAmbient f g h i :=
  pullback.map _ _ _ _ (correspondenceTripleInclusion f g h) (𝟙 _) (𝟙 Z)
    (by simp [correspondenceTripleTarget, correspondenceAmbientTarget]) (by simp)

/-- The first-pair coordinate of the fourfold-to-second-diagonal map. -/
@[reassoc (attr := simp)] theorem correspondenceFourfoldToSecondAmbient_fst :
    correspondenceFourfoldToSecondAmbient f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) ≫
      correspondenceTripleInclusion f g h := pullback.lift_fst _ _ _

/-- The final adjacent-product coordinate is unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceFourfoldToSecondAmbient_snd :
    correspondenceFourfoldToSecondAmbient f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceFourfoldToSecondAmbient, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- The second ambient diagonal keeps the first ambient coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondAmbientInclusion_fst :
    correspondenceSecondAmbientInclusion f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondAmbientInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second ambient diagonal keeps the last adjacent-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondAmbientInclusion_snd :
    correspondenceSecondAmbientInclusion f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondAmbientInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The two diagonal orders define the same actual six-factor morphism. -/
@[reassoc] theorem correspondenceFourfold_diagonals_comm :
    correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i =
    correspondenceFourfoldToSecondAmbient f g h i ≫
      correspondenceSecondAmbientInclusion f g h i := by
  apply pullback.hom_ext <;> simp

/-- The second-diagonal base change still uses the original first middle inclusion. -/
theorem correspondenceFourfold_secondBaseChange :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i))
      (correspondenceFourfoldToSecondAmbient f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i)) := by
  apply IsPullback.flip
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback
    (correspondenceAmbientTarget f g h) (pullback.fst h i)).flip)
  · simpa [correspondenceAmbientTarget, correspondenceTripleTarget] using
      (IsPullback.of_hasPullback (correspondenceTripleTarget f g h) (pullback.fst h i)).flip
  · exact correspondenceFourfoldToSecondAmbient_fst f g h i

/-- The fourfold product is the actual Cartesian intersection of the two
middle diagonals in the original six-factor ambient. -/
theorem correspondenceFourfold_diagonals_isPullback :
    IsPullback (correspondenceSecondDiagonalInclusion f g h i)
      (correspondenceFourfoldToSecondAmbient f g h i)
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceSecondAmbientInclusion f g h i) := by
  apply IsPullback.of_right (t := correspondenceFirstDiagonal_baseChange f g h i)
  · simpa only [correspondenceSecondDiagonalInclusion_fst,
      correspondenceSecondAmbientInclusion_fst] using
        correspondenceFourfold_secondBaseChange f g h i
  · exact correspondenceFourfold_diagonals_comm f g h i

/-- The first ideal is literally the pullback of the Y-diagonal ideal. -/
theorem ker_correspondenceFirstDiagonal [IsSeparated g] :
    (correspondenceFirstDiagonalInclusion f g h i).ker =
      (pullback.diagonal g).ker.comap (correspondenceSixfoldFirstMiddlePair f g h i) := by
  let sq := (correspondenceSixfoldFirstDiagonal_isPullback f g h i).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The second ideal is literally the pullback of the Z-diagonal ideal. -/
theorem ker_correspondenceSecondDiagonal [IsSeparated h] :
    (correspondenceSecondAmbientInclusion f g h i).ker =
      (pullback.diagonal h).ker.comap (correspondenceSixfoldSecondMiddlePair f g h i) := by
  let sq := (correspondenceSixfoldSecondDiagonal_isPullback f g h i).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The full fourfold diagonal kernel is the sum of both actual middle ideals. -/
theorem ker_correspondenceFourfoldDiagonal [IsSeparated g] [IsSeparated h] :
    (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        (correspondenceSecondAmbientInclusion f g h i).ker :=
  Scheme.Hom.ker_comp_eq_sup_of_isPullback _ _ _ _ (correspondenceFourfold_diagonals_isPullback f
    g h i)


end Stacks.Chow
