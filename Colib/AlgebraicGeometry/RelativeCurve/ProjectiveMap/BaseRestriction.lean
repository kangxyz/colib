/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BaseRestriction
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-! # The actual finite projective map after affine base restriction

The map is constructed by the native projective-space Cartesian square. It is
not a schematic comparison with the legacy projective model. The final ring is
the actual section ring of the chosen base open.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {N S : Scheme.{u}} (n : ℕ) (π : N ⟶ projectiveSpaceOver n S) (T : S.Opens)

/-- The actual map into projective space over the retained base open. -/
def projectiveMapRestrict :
    ((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme ⟶ projectiveSpaceOver n T.toScheme :=
  (isPullback_projectiveSpaceOverMap n T.ι).lift
    (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).ι ≫ π)
    ((π ≫ (projectiveSpaceOver n S ↘ S)) ∣_ T)
    (by
      change (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).ι ≫ π) ≫
        (projectiveSpaceOver n S ↘ S) = ((π ≫ (projectiveSpaceOver n S ↘ S)) ∣_ T) ≫ T.ι
      exact (Category.assoc _ _ _).trans (morphismRestrict_ι _ _).symm)

@[reassoc (attr := simp)]
theorem projectiveMapRestrict_map :
    projectiveMapRestrict n π T ≫ projectiveSpaceOverMap n T.ι =
      ((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).ι ≫ π :=
  (isPullback_projectiveSpaceOverMap n T.ι).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem projectiveMapRestrict_projection :
    projectiveMapRestrict n π T ≫ (projectiveSpaceOver n T.toScheme ↘ T.toScheme) =
      (π ≫ (projectiveSpaceOver n S ↘ S)) ∣_ T :=
  (isPullback_projectiveSpaceOverMap n T.ι).lift_snd _ _ _

/-- The projective map is restricted by an actual Cartesian square. -/
theorem projectiveMapRestrict_isPullback :
    IsPullback (projectiveMapRestrict n π T)
      ((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).ι
      (projectiveSpaceOverMap n T.ι) π := by
  have H : IsPullback (projectiveSpaceOverMap n T.ι)
      (projectiveSpaceOver n T.toScheme ↘ T.toScheme)
      (projectiveSpaceOver n S ↘ S) T.ι := isPullback_projectiveSpaceOverMap n T.ι
  apply IsPullback.of_right
    (h₁₂ := projectiveSpaceOver n T.toScheme ↘ T.toScheme) ?_
    (projectiveMapRestrict_map n π T) H.flip
  simpa only [projectiveMapRestrict_projection] using
    isPullback_morphismRestrict (π ≫ (projectiveSpaceOver n S ↘ S)) T

instance [IsFinite π] : IsFinite (projectiveMapRestrict n π T) :=
  MorphismProperty.of_isPullback (projectiveMapRestrict_isPullback n π T).flip
    (inferInstance : IsFinite π)

variable [IsAffine T.toScheme]

/-- The same finite map over the literal ring Γ(T,O), not a replacement base. -/
def finiteProjectiveBaseRestriction :
    ((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme ⟶
      projectiveSpaceOverRing n Γ(T.toScheme, ⊤) :=
  projectiveMapRestrict n π T ≫ projectiveSpaceOverMap n T.toScheme.isoSpec.hom

instance [IsFinite π] : IsFinite (finiteProjectiveBaseRestriction n π T) := by
  have : IsIso (projectiveSpaceOverMap n T.toScheme.isoSpec.hom) :=
    (isPullback_projectiveSpaceOverMap n T.toScheme.isoSpec.hom).isIso_fst_of_isIso
  unfold finiteProjectiveBaseRestriction
  infer_instance

@[reassoc]
theorem finiteProjectiveBaseRestriction_toSpec :
    finiteProjectiveBaseRestriction n π T ≫
      (projectiveSpaceOverRing n Γ(T.toScheme, ⊤) ↘ Spec Γ(T.toScheme, ⊤)) =
      ((π ≫ (projectiveSpaceOver n S ↘ S)) ∣_ T) ≫ T.toScheme.isoSpec.hom := by
  let p := projectiveMapRestrict n π T
  let g := T.toScheme.isoSpec.hom
  let P := projectiveSpaceOver n T.toScheme ↘ T.toScheme
  let Q := projectiveSpaceOverRing n Γ(T.toScheme, ⊤) ↘ Spec Γ(T.toScheme, ⊤)
  change (p ≫ projectiveSpaceOverMap n g) ≫ Q = _
  calc
    _ = p ≫ (projectiveSpaceOverMap n g ≫ Q) := Category.assoc _ _ _
    _ = p ≫ (P ≫ g) := congrArg (fun m => p ≫ m) (projectiveSpaceOverMap_fst n g)
    _ = (p ≫ P) ≫ g := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun m => m ≫ g) (projectiveMapRestrict_projection n π T)

/-- Integrality uses the specified retained point; normality uses the literal
open restriction of the original normal compactification. -/
theorem finiteProjectiveBaseRestriction_properties [IsIntegral N] [IsNormal N]
    [IsLocallyNoetherian N] [IsFinite π] (x : N)
    (hx : (π ≫ (projectiveSpaceOver n S ↘ S)) x ∈ T) :
    IsIntegral (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme) ∧
    IsLocallyNoetherian (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme) ∧
    IsNormal (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme) ∧
    IsFinite (finiteProjectiveBaseRestriction n π T) ∧
    IsProper (finiteProjectiveBaseRestriction n π T ≫
      (projectiveSpaceOverRing n Γ(T.toScheme, ⊤) ↘ Spec Γ(T.toScheme, ⊤))) := by
  let : Nonempty (((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).toScheme) := ⟨⟨x, hx⟩⟩
  exact ⟨isIntegral_of_isOpenImmersion
    ((π ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ T).ι, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- Smoothness belongs to the unchanged retained structural map. -/
theorem finiteProjectiveBaseRestriction_retained_smooth
    (V : N.Opens)
    [SmoothOfRelativeDimension 1 (V.ι ≫ π ≫ (projectiveSpaceOver n S ↘ S))] :
    SmoothOfRelativeDimension 1
      (retainedBaseInclusion (π ≫ (projectiveSpaceOver n S ↘ S)) T V ≫
        finiteProjectiveBaseRestriction n π T ≫
          (projectiveSpaceOverRing n Γ(T.toScheme, ⊤) ↘ Spec Γ(T.toScheme, ⊤))) := by
  rw [finiteProjectiveBaseRestriction_toSpec]
  exact retainedBase_smooth _ T V

end AlgebraicGeometry.Scheme.RelativeCurve
