/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The actual flat ambient projection for the remaining intersection

The first-diagonal ambient is `(X × Y × Z) × (Z × W)`. Forgetting `Y`
gives `(X × Z) × (Z × W)`. Flatness belongs to this ambient map and is
proved by Cartesian squares; it is never imposed on the finite support or
its scheme-theoretic image. Its restriction to the full first-stage
incidence times the third support is finite.

These maps use the selected native pullbacks, with their scheme structures.
The only categorical suppliers are Mathlib's pullback pasting and stability
under base change. The analogous Stacks `tripleProj₁₃` uses a different
parenthesization over a field; here the actual selected correspondence
triple product is retained, over an arbitrary base scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The actual projection from the adjacent-pair triple product to `X × Z`. -/
def correspondenceTripleOuterProjection : correspondenceTripleProduct f g h ⟶ pullback f h :=
  pullback.lift
    (pullback.fst (pullback.snd f g) (pullback.fst g h) ≫ pullback.fst f g)
    (correspondenceTripleTarget f g h) (by
      dsimp only [correspondenceTripleTarget]
      simp only [Category.assoc, pullback.condition (f := f) (g := g)]
      rw [← Category.assoc, pullback.condition, Category.assoc,
        pullback.condition (f := g) (g := h)])

@[reassoc (attr := simp)]
theorem correspondenceTripleOuterProjection_fst :
    correspondenceTripleOuterProjection f g h ≫ pullback.fst f h =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceTripleOuterProjection_snd :
    correspondenceTripleOuterProjection f g h ≫ pullback.snd f h =
      correspondenceTripleTarget f g h :=
  pullback.lift_snd _ _ _

/-- The actual outer projection is a base change of `X × Y → X`. -/
theorem correspondenceTripleOuterProjection_isPullback :
    IsPullback (correspondenceTripleOuterProjection f g h)
      (pullback.fst (pullback.snd f g) (pullback.fst g h))
      (pullback.fst f h) (pullback.fst f g) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd f h) (h₂₂ := f) (v₁₃ := h) ?_
    (correspondenceTripleOuterProjection_fst f g h) (IsPullback.of_hasPullback f h).flip
  rw [correspondenceTripleOuterProjection_snd, pullback.condition (f := f) (g := g)]
  exact (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g h)).flip.paste_horiz
    (IsPullback.of_hasPullback g h).flip

instance flat_correspondenceTripleOuterProjection [Flat g] :
    Flat (correspondenceTripleOuterProjection f g h) :=
  MorphismProperty.of_isPullback (correspondenceTripleOuterProjection_isPullback f g h).flip
    inferInstance

instance quasiCompact_correspondenceTripleOuterProjection [QuasiCompact g] :
    QuasiCompact (correspondenceTripleOuterProjection f g h) :=
  MorphismProperty.of_isPullback (correspondenceTripleOuterProjection_isPullback f g h).flip
    inferInstance

instance quasiSeparated_correspondenceTripleOuterProjection [QuasiSeparated g] :
    QuasiSeparated (correspondenceTripleOuterProjection f g h) :=
  MorphismProperty.of_isPullback (correspondenceTripleOuterProjection_isPullback f g h).flip
    inferInstance

/-- The ambient projection forgetting the original middle factor, before the
remaining diagonal is imposed. -/
def correspondenceRemainingProjection : correspondenceFirstDiagonal f g h i ⟶
    correspondenceIntersectionAmbient f h i :=
  pullback.map _ _ _ _ (correspondenceTripleOuterProjection f g h)
    (𝟙 (pullback h i)) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem correspondenceRemainingProjection_fst :
    correspondenceRemainingProjection f g h i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ correspondenceTripleOuterProjection f g h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceRemainingProjection_snd :
    correspondenceRemainingProjection f g h i ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [correspondenceRemainingProjection, pullback.map, pullback.lift_snd,
    Category.comp_id]

instance flat_correspondenceRemainingProjection [Flat g] :
    Flat (correspondenceRemainingProjection f g h i) := by
  unfold correspondenceRemainingProjection
  exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance (by simp) (by simp)

instance quasiCompact_correspondenceRemainingProjection [QuasiCompact g] :
    QuasiCompact (correspondenceRemainingProjection f g h i) := by
  unfold correspondenceRemainingProjection
  exact MorphismProperty.pullbackMap (P := @QuasiCompact)
    inferInstance inferInstance (by simp) (by simp)

instance quasiSeparated_correspondenceRemainingProjection [QuasiSeparated g] :
    QuasiSeparated (correspondenceRemainingProjection f g h i) := by
  unfold correspondenceRemainingProjection
  exact MorphismProperty.pullbackMap (P := @QuasiSeparated)
    inferInstance inferInstance (by simp) (by simp)

/-- Forgetting `Y` after imposing the remaining diagonal. -/
def correspondenceFourfoldRemainingProjection : correspondenceFourfoldProduct f g h i ⟶
    correspondenceTripleProduct f h i :=
  pullback.map _ _ _ _ (correspondenceTripleOuterProjection f g h)
    (𝟙 (pullback h i)) (𝟙 Z) (by simp) (by simp)

/-- The two remaining middle coordinates before imposing their diagonal. -/
abbrev correspondenceFirstRemainingMiddlePair : correspondenceFirstDiagonal f g h i ⟶
    pullback h h :=
  pullback.map _ _ h h (correspondenceTripleTarget f g h) (pullback.fst h i) (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem correspondenceRemainingProjection_middlePair :
    correspondenceRemainingProjection f g h i ≫ correspondenceMiddlePair f h i =
      correspondenceFirstRemainingMiddlePair f g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceMiddlePair, correspondenceFirstRemainingMiddlePair, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceFourfoldRemainingProjection_middle :
    correspondenceFourfoldRemainingProjection f g h i ≫ correspondenceTripleMiddle f h i =
      pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) ≫
        correspondenceTripleTarget f g h := by
  simp [correspondenceFourfoldRemainingProjection, correspondenceTripleMiddle, Category.assoc]

/-- The two orders of forgetting the factor and imposing the diagonal agree. -/
@[reassoc]
theorem correspondenceFourfoldRemainingProjection_inclusion :
    correspondenceFourfoldRemainingProjection f g h i ≫ correspondenceTripleInclusion f h i =
      correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceRemainingProjection f g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceFourfoldRemainingProjection, Category.assoc]

/-- The actual remaining diagonal is the Cartesian pullback of the target
remaining diagonal, retaining its full scheme structure. -/
theorem correspondenceRemainingDiagonal_isPullback :
    IsPullback (correspondenceFourfoldRemainingProjection f g h i)
      (correspondenceSecondDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f h i) (correspondenceRemainingProjection f g h i) := by
  refine IsPullback.of_right (h₁₂ := correspondenceTripleMiddle f h i)
    (h₂₂ := correspondenceMiddlePair f h i) (v₁₃ := pullback.diagonal h) ?_
    (correspondenceFourfoldRemainingProjection_inclusion f g h i)
    (correspondenceTriple_isPullback f h i)
  rw [correspondenceFourfoldRemainingProjection_middle,
    correspondenceRemainingProjection_middlePair]
  exact pullback_map_diagonal_isPullback
    (correspondenceTripleTarget f g h) (pullback.fst h i) h

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- On the full incidence, the outer projection is the original finite map. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceInclusion_outerProjection :
    correspondenceIncidenceInclusion f g h z w ≫ correspondenceTripleOuterProjection f g h =
      correspondenceIncidenceMap f g h z w := by
  apply pullback.hom_ext
  · simp [correspondenceIncidenceLeft]
  · simp [correspondenceTripleTarget, correspondenceIncidenceRight]

/-- The whole first-stage support, including nilpotents, maps to the remaining
four-factor ambient by the exterior product of the original finite map. -/
def correspondenceRemainingSupportMap :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIntersectionAmbient f h i :=
  pullback.map _ _ _ _ (correspondenceIncidenceMap f g h z w)
    (integralComponentAt v).subschemeι (𝟙 S) (by simp) (by simp)

/-- The finite restriction is the restriction of the verified flat ambient map. -/
@[reassoc]
theorem correspondenceRemainingSupportMap_eq :
    correspondenceLeftIntermediateSupportInclusion f g h i z w v ≫
        correspondenceRemainingProjection f g h i =
      correspondenceRemainingSupportMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceRemainingSupportMap, Category.assoc]

/-- Only the support restriction is finite; the ambient map need not be proper. -/
theorem isFinite_correspondenceRemainingSupportMap [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceRemainingSupportMap f g h i z w v) := by
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  unfold correspondenceRemainingSupportMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp) (by simp)

end Stacks.Chow
