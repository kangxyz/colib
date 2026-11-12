/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The unchanged affine retained open after actual base restriction -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {N S : Scheme.{u}} (q : N ⟶ S) (T : S.Opens)

/-- The retained open uses the original source and the original base restriction. -/
abbrev retainedBaseOpen (V : N.Opens) := (V.ι ≫ q) ⁻¹ᵁ T

/-- Its inclusion into the actual restricted compactification. -/
def retainedBaseInclusion (V : N.Opens) :
    (retainedBaseOpen q T V).toScheme ⟶ (q ⁻¹ᵁ T).toScheme :=
  V.ι ∣_ q ⁻¹ᵁ T

instance (V : N.Opens) : IsOpenImmersion (retainedBaseInclusion q T V) := by
  dsimp [retainedBaseInclusion]
  infer_instance

@[reassoc]
theorem retainedBaseInclusion_ι (V : N.Opens) :
    retainedBaseInclusion q T V ≫ (q ⁻¹ᵁ T).ι =
      (retainedBaseOpen q T V).ι ≫ V.ι := morphismRestrict_ι _ _

@[reassoc]
theorem retainedBaseInclusion_projection (V : N.Opens) :
    retainedBaseInclusion q T V ≫ q ∣_ T = (V.ι ≫ q) ∣_ T :=
  (morphismRestrict_comp V.ι q T).symm

variable [IsAffine T.toScheme]

/-- The original retained smooth map over the actual ring of the base open. -/
theorem retainedBase_smooth (V : N.Opens) [SmoothOfRelativeDimension 1 (V.ι ≫ q)] :
    SmoothOfRelativeDimension 1
      (retainedBaseInclusion q T V ≫ q ∣_ T ≫ T.toScheme.isoSpec.hom) := by
  rw [← Category.assoc, retainedBaseInclusion_projection]
  have : SmoothOfRelativeDimension 1 ((V.ι ≫ q) ∣_ T) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict (V.ι ≫ q) T).flip inferInstance
  exact smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _

/-- Affineness is retained on the literal preimage, not on a replacement localization model. -/
theorem retainedBase_affine [IsAffine S] (V : N.Opens) [IsAffine V.toScheme] :
    IsAffine (retainedBaseOpen q T V).toScheme :=
  IsAffineOpen.preimage (show IsAffineOpen T from (inferInstance : IsAffine T.toScheme)) (V.ι ≫ q)

omit [IsAffine T.toScheme] in
/-- The original retained point remains literally the same point in both open restrictions. -/
theorem retainedBase_point (V : N.Opens) (x : N) (hxV : x ∈ V) (hxT : q x ∈ T) :
    retainedBaseInclusion q T V ⟨⟨x, hxV⟩, hxT⟩ = ⟨x, hxT⟩ := by
  apply Subtype.ext
  exact congrArg (fun f => f ⟨⟨x, hxV⟩, hxT⟩) (retainedBaseInclusion_ι q T V)


end AlgebraicGeometry.Scheme.RelativeCurve
