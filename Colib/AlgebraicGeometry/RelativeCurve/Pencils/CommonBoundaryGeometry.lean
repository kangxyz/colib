/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundarySourceChange
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullGraphBoundaryFrame

/-!
# The two independent source maps and their whole common boundary

The original first and second section pairs remain on different products. The
common product pulls them back along the actual alpha and beta maps. Both whole
boundary components commute with those maps. This adapts only the native
scheme-map part of the original `Pencils/Common/Boundary.lean` and
`BoundaryInclusions.lean`; the unique product constructor is retainedSourceChange.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

/-- The structure map of the common source through the lambda-source curve. -/
abbrev commonProjection := α ≫ (j ≫ π)
/-- The compactification pulled back to the common source. -/
abbrev commonAmbient := pullback (commonProjection π j α) π
/-- The infinity boundary pulled back to the common ambient scheme. -/
abbrev commonInfinity := pullback (pullback.snd (commonProjection π j α) π) d
/-- The zero boundary over the common source, defined using `s`. -/
abbrev commonZero := pullback (commonProjection π j α) (s ≫ j ≫ π)
/-- The coproduct of the common infinity and zero boundaries. -/
abbrev commonBoundary := commonInfinity π j α d ⨿ commonZero π j α s

include hq h in
lemma commonProjection_fixed : commonProjection π j α = β ≫ (a ≫ q) := by
  dsimp only [commonProjection]
  rw [hq, ← Category.assoc, h, Category.assoc]

/-- The map from the common ambient scheme to the lambda ambient scheme induced by `α`. -/
abbrev commonToLambda : commonAmbient π j α ⟶ pullback (j ≫ π) π :=
  retainedSourceChange (j ≫ π) (commonProjection π j α) π α rfl
/-- The map from the common ambient scheme to the psi ambient scheme induced by `β`. -/
abbrev commonToPsi : commonAmbient π j α ⟶ pullback (a ≫ q) π :=
  retainedSourceChange (a ≫ q) (commonProjection π j α) π β
    (commonProjection_fixed q π j p hq a α β h).symm

/-- The map of the common zero boundary into the common ambient scheme induced by `s ≫ j`. -/
def commonZeroInclusion : commonZero π j α s ⟶ commonAmbient π j α :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s ≫ j)
    (by simpa only [Category.assoc] using (pullback.condition
      (f := commonProjection π j α) (g := s ≫ j ≫ π)))
/-- The map of the coproduct boundary into the common ambient scheme. -/
abbrev commonBoundaryInclusion : commonBoundary π j α s d ⟶ commonAmbient π j α :=
  coprod.desc (pullback.fst _ _) (commonZeroInclusion π j α s)

/-- The zero-boundary source-change map induced by `α`. -/
def commonZeroToLambda : commonZero π j α s ⟶ pullback (j ≫ π) (s ≫ j ≫ π) :=
  retainedSourceChange (j ≫ π) (commonProjection π j α) (s ≫ j ≫ π) α rfl

/-- The zero-boundary source-change map induced by `β` and the compatible boundary square. -/
def commonZeroToPsi : commonZero π j α s ⟶ pullback (a ≫ q) (z ≫ q) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _) (by
    have hz : s ≫ j ≫ π = z ≫ q := by rw [hq, ← Category.assoc, hs]
    rw [Category.assoc, ← commonProjection_fixed q π j p hq a α β h, pullback.condition]
    exact congrArg (fun f => pullback.snd (commonProjection π j α) (s ≫ j ≫ π) ≫ f) hz)

/-- The coproduct of the infinity and zero source-change maps to the lambda boundary. -/
def commonBoundaryToLambda : commonBoundary π j α s d ⟶
    (pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) :=
  coprod.map (constantInfinitySourceMap α (j ≫ π) π (commonProjection π j α) rfl d)
    (commonZeroToLambda π j α s)

/-- The coproduct of the infinity and zero source-change maps to the psi boundary. -/
def commonBoundaryToPsi : commonBoundary π j α s d ⟶
    (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) :=
  coprod.map (constantInfinitySourceMap β (a ≫ q) π (commonProjection π j α)
    (commonProjection_fixed q π j p hq a α β h) d)
    (commonZeroToPsi q π j p hq a α β h z s hs)

lemma commonBoundaryToLambda_inclusion :
    commonBoundaryToLambda π j α s d ≫
      coprod.desc (infinityProductMap π j d) (markedProductMap π j s) =
    commonBoundaryInclusion π j α s d ≫ commonToLambda π j α := by
  apply coprod.hom_ext
  · simp [commonBoundaryToLambda, infinityProductMap, commonBoundaryInclusion,
      commonToLambda]
  · simp only [commonBoundaryToLambda, coprod.inr_map_assoc, coprod.inr_desc,
      commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;> simp [commonZeroToLambda, markedProductMap,
      commonZeroInclusion, commonToLambda, Category.assoc]

lemma commonToLambda_isPullback :
    IsPullback (commonToLambda π j α) (pullback.fst (commonProjection π j α) π)
      (pullback.fst (j ≫ π) π) α := retainedSourceChange_isPullback _ _ _ α rfl
lemma commonToPsi_isPullback :
    IsPullback (commonToPsi q π j p hq a α β h) (pullback.fst (commonProjection π j α) π)
      (pullback.fst (a ≫ q) π) β :=
  retainedSourceChange_isPullback _ _ _ β
    (commonProjection_fixed q π j p hq a α β h).symm

/-- The map of the psi zero boundary into its ambient scheme induced by `s ≫ j`. -/
def psiZeroInclusion : pullback (a ≫ q) (z ≫ q) ⟶ pullback (a ≫ q) π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s ≫ j) (by
    rw [Category.assoc, Category.assoc, hq, ← Category.assoc s, hs]
    exact pullback.condition)

/-- The coproduct map from the psi infinity and zero boundaries into the psi ambient scheme. -/
abbrev psiBoundaryInclusion :
    (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) ⟶ pullback (a ≫ q) π :=
  coprod.desc (pullback.fst _ _) (psiZeroInclusion q π j p hq a z s hs)

lemma commonBoundaryToPsi_inclusion :
    commonBoundaryToPsi q π j p hq a α β h z s hs d ≫
      psiBoundaryInclusion q π j p hq a z s hs d =
    commonBoundaryInclusion π j α s d ≫ commonToPsi q π j p hq a α β h := by
  apply coprod.hom_ext
  · simp [commonBoundaryToPsi, psiBoundaryInclusion, commonBoundaryInclusion, commonToPsi]
  · simp only [commonBoundaryToPsi, psiBoundaryInclusion, coprod.inr_map_assoc,
      coprod.inr_desc, commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonZeroToPsi, psiZeroInclusion, commonZeroInclusion, commonToPsi, Category.assoc]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
