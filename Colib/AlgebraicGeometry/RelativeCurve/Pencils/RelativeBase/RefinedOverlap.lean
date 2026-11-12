/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedGeometry
/-! # The actual refined overlap map to the original retained target over V -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X C Y A T : Scheme.{u}} (q : X ⟶ S) (U : X.Opens) (V : S.Opens)
  (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (v : T ⟶ C) (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

include hq hφ in
/-- The original overlap target map after the explicitly simultaneous source change. -/
theorem overlapTarget_base :
    overlapToOriginal q U V p a ≫ φ ≫ v ≫ π =
      pullback.fst (firstMap q U V p) (secondMap q U V a) ≫
        firstMap q U V p ≫ parameterProjection q U V ≫ V.ι := by
  rw [← Category.assoc φ v π, hφ]
  simp only [Category.assoc, hq, parameterProjection_base, firstMap,
    pullback.condition_assoc, overlapToOriginal_snd_assoc]

include hq hφ in
/-- This map lands in the entire original retained target over V. It is not
restricted by the chosen parameter neighborhood U. -/
def refinedTargetMap : overlap q U V p a ⟶ (sourceBaseOpen π V v).toScheme :=
  IsOpenImmersion.lift (sourceBaseOpen π V v).ι
    (overlapToOriginal q U V p a ≫ φ) (by
      rintro _ ⟨b, rfl⟩
      refine ⟨⟨(overlapToOriginal q U V p a ≫ φ) b, ?_⟩, rfl⟩
      change (overlapToOriginal q U V p a ≫ φ ≫ v ≫ π) b ∈ V
      rw [overlapTarget_base q U V π j p hq a v φ hφ]
      exact (parameterProjection q U V
        (firstMap q U V p (pullback.fst (firstMap q U V p) (secondMap q U V a) b))).property)

@[reassoc (attr := simp)]
theorem refinedTargetMap_original :
    refinedTargetMap q U V π j p hq a v φ hφ ≫ (sourceBaseOpen π V v).ι =
      overlapToOriginal q U V p a ≫ φ := IsOpenImmersion.lift_fac _ _ _

/-- The exact original target equation survives the simultaneous refinement. -/
@[reassoc (attr := simp)]
theorem refinedTargetMap_inclusion :
    refinedTargetMap q U V π j p hq a v φ hφ ≫ sourceBaseMap π V v =
      pullback.fst (firstMap q U V p) (secondMap q U V a) ≫
        firstInclusion q U V π j p hq := by
  apply (cancel_mono (compactificationOpen π V).ι).mp
  simp only [Category.assoc, sourceBaseMap_original, refinedTargetMap_original_assoc,
    hφ, overlapToOriginal_fst_assoc, firstInclusion_original]

/-- The literal source square used in both independent signed corrections. -/
theorem refinedOverlap_square :
    pullback.fst (firstMap q U V p) (secondMap q U V a) ≫ firstMap q U V p =
      pullback.snd (firstMap q U V p) (secondMap q U V a) ≫ secondMap q U V a :=
  pullback.condition

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
