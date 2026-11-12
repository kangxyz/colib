/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GraphNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The actual simultaneous parameter and base refinement

The parameter becomes U intersect q inverse V. Both covering sources are the
literal pullbacks along its inclusion, and their overlap uses these same maps.
The whole mark over V is Cartesian over this parameter because U contains that
entire mark. The original retained target is restricted only over V. No hidden
restriction of one side, no chosen-point replacement and no reduced mark occurs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X Y A Z : Scheme.{u}} (q : X ⟶ S) (U : X.Opens) (V : S.Opens)

/-- The explicit common parameter open, not a new retained target. -/
abbrev parameterOpen : X.Opens := U ⊓ q ⁻¹ᵁ V

/-- Its actual map to the common base open. -/
def parameterProjection : (parameterOpen q U V).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ((parameterOpen q U V).ι ≫ q) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨q x.val, x.property.2⟩, rfl⟩)

@[reassoc (attr := simp)]
theorem parameterProjection_base :
    parameterProjection q U V ≫ V.ι = (parameterOpen q U V).ι ≫ q :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both affine opens are kept in the intersection; no quasi-affine-to-affine
substitution is used. -/
theorem parameterOpen_affine [IsAffine X] [IsAffine S]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (parameterOpen q U V) :=
  hU.inf (hV.preimage q)

/-- The parameter-to-U map exhibits the projection as the actual base change
of the original relative curve restricted to U. -/
def parameterToSource : (parameterOpen q U V).toScheme ⟶ U.toScheme :=
  X.homOfLE inf_le_left

instance : IsOpenImmersion (parameterToSource q U V) := by
  unfold parameterToSource
  infer_instance

@[reassoc (attr := simp)]
theorem parameterToSource_original :
    parameterToSource q U V ≫ U.ι = (parameterOpen q U V).ι := by
  simp [parameterToSource]

/-- The smooth relative curve is transported through a genuine Cartesian square. -/
theorem parameterProjection_isPullback :
    IsPullback (parameterProjection q U V) (parameterToSource q U V)
      V.ι (U.ι ≫ q) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · simp only [parameterToSource_original_assoc, parameterProjection_base]
  · ext x
    have hx : U.ι x ∈ U := x.property
    simp [parameterToSource, parameterOpen, hx]

instance [IsSeparated q] : IsSeparated (parameterProjection q U V) :=
  MorphismProperty.of_isPullback (parameterProjection_isPullback q U V).flip inferInstance

instance [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1 (parameterProjection q U V) := by
  have : SmoothOfRelativeDimension 1 (U.ι ≫ q) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  exact MorphismProperty.of_isPullback
    (parameterProjection_isPullback q U V).flip inferInstance

variable (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U)

/-- The full original marked scheme over the chosen base, with all nilpotents. -/
abbrev markOpen : Z.Opens := (z ≫ q) ⁻¹ᵁ V

/-- Its original inclusion factors through the same parameter refinement. -/
def markToParameter : (markOpen q V z).toScheme ⟶ (parameterOpen q U V).toScheme :=
  IsOpenImmersion.lift (parameterOpen q U V).ι ((markOpen q V z).ι ≫ z) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨z b.val, h b.val b.property, b.property⟩, rfl⟩)

@[reassoc (attr := simp)]
theorem markToParameter_original :
    markToParameter q U V z h ≫ (parameterOpen q U V).ι = (markOpen q V z).ι ≫ z :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem markToParameter_base :
    markToParameter q U V z h ≫ parameterProjection q U V = (z ≫ q) ∣_ V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, parameterProjection_base, morphismRestrict_ι,
    markToParameter_original_assoc]

/-- The mark is the literal pullback of the whole original mark, not a smaller
subscheme with the same selected point. -/
theorem markToParameter_isPullback :
    IsPullback (markToParameter q U V z h) (markOpen q V z).ι
      (parameterOpen q U V).ι z := by
  apply IsOpenImmersion.isPullback _ _ _ _ (markToParameter_original q U V z h).symm
  ext b
  simp only [Scheme.Opens.opensRange_ι]
  change (z b ∈ U ∧ (z ≫ q) b ∈ V) ↔ (z ≫ q) b ∈ V
  exact ⟨And.right, fun hb => ⟨h b hb, hb⟩⟩

/-- The finite map remains finite on the entire base-restricted marked scheme. -/
theorem markToParameter_finite [IsFinite (z ≫ q)] :
    IsFinite (markToParameter q U V z h ≫ parameterProjection q U V) := by
  rw [markToParameter_base]
  infer_instance

variable (p : Y ⟶ X) (a : A ⟶ X)

/-- The first original source restricted by the actual common parameter. -/
abbrev firstSource := pullback p (parameterOpen q U V).ι
/-- The entire second original source over that same parameter. -/
abbrev secondSource := pullback a (parameterOpen q U V).ι
/-- Its literal projection into the parameter. -/
abbrev firstMap := pullback.snd p (parameterOpen q U V).ι
/-- Its literal projection into the parameter. -/
abbrev secondMap := pullback.snd a (parameterOpen q U V).ι
/-- Both source maps define one actual common overlap. -/
abbrev overlap := pullback (firstMap q U V p) (secondMap q U V a)

/-- The actual overlap map back to the original overlap, preserving both legs. -/
def overlapToOriginal : overlap q U V p a ⟶ pullback p a :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst p (parameterOpen q U V).ι)
    (pullback.snd _ _ ≫ pullback.fst a (parameterOpen q U V).ι) (by
      rw [Category.assoc, pullback.condition, pullback.condition_assoc,
        Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem overlapToOriginal_fst :
    overlapToOriginal q U V p a ≫ pullback.fst p a =
      pullback.fst _ _ ≫ pullback.fst p (parameterOpen q U V).ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem overlapToOriginal_snd :
    overlapToOriginal q U V p a ≫ pullback.snd p a =
      pullback.snd _ _ ≫ pullback.fst a (parameterOpen q U V).ι := pullback.lift_snd _ _ _

/-- The source change leaves the original source square literally commutative. -/
theorem overlap_original_square :
    (pullback.fst (firstMap q U V p) (secondMap q U V a) ≫
        pullback.fst p (parameterOpen q U V).ι) ≫ p =
      (pullback.snd (firstMap q U V p) (secondMap q U V a) ≫
        pullback.fst a (parameterOpen q U V).ι) ≫ a := by
  rw [← overlapToOriginal_fst, ← overlapToOriginal_snd, Category.assoc, Category.assoc,
    pullback.condition]

/-- The original full closed lift survives this exact common restriction. -/
def closedLift (s : Z ⟶ Y) (hs : s ≫ p = z) :
    (markOpen q V z).toScheme ⟶ firstSource q U V p :=
  pullback.lift ((markOpen q V z).ι ≫ s) (markToParameter q U V z h)
    (by rw [Category.assoc, hs, markToParameter_original])

@[reassoc (attr := simp)]
theorem closedLift_first (s : Z ⟶ Y) (hs : s ≫ p = z) :
    closedLift q U V z h p s hs ≫ pullback.fst p (parameterOpen q U V).ι =
      (markOpen q V z).ι ≫ s := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem closedLift_parameter (s : Z ⟶ Y) (hs : s ≫ p = z) :
    closedLift q U V z h p s hs ≫ firstMap q U V p = markToParameter q U V z h :=
  pullback.lift_snd _ _ _

/-- The identity-on-mark Cartesian condition is retained for the entire mark. -/
theorem closedLift_isPullback (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (closedLift q U V z h p s hs) (𝟙 _)
      (firstMap q U V p) (markToParameter q U V z h) := by
  have Hbig := (IsPullback.of_id_snd (f := (markOpen q V z).ι)).paste_horiz H
  rw [← markToParameter_original q U V z h] at Hbig
  apply IsPullback.of_right (h₁₂ := pullback.fst p (parameterOpen q U V).ι) ?_ ?_
    (IsPullback.of_hasPullback p (parameterOpen q U V).ι)
  · simpa only [closedLift_first] using Hbig
  · simp only [closedLift_parameter, Category.id_comp]

/-- The original puncture stays disjoint from the entire mark after the same
restriction of both sides. -/
theorem puncture_disjoint (ha : Disjoint (Set.range a) (Set.range z)) :
    Disjoint (Set.range (secondMap q U V a)) (Set.range (markToParameter q U V z h)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun x => (parameterOpen q U V).ι x) hb
  change (markToParameter q U V z h ≫ (parameterOpen q U V).ι) b =
    (secondMap q U V a ≫ (parameterOpen q U V).ι) y at he
  rw [markToParameter_original, ← pullback.condition] at he
  exact Set.disjoint_iff_forall_ne.mp ha ⟨_, rfl⟩ ⟨_, rfl⟩ he.symm

/-- The old puncture/mark cover remains a cover, using every point of both schemes. -/
theorem puncture_cover (ha : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z) :
    ∀ x : (parameterOpen q U V).toScheme,
      x ∈ Set.range (secondMap q U V a) ∨ x ∈ Set.range (markToParameter q U V z h) := by
  intro x
  rcases ha x.val with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback a (parameterOpen q U V).ι) b x hb
    exact ⟨y, hy⟩
  · right
    have hbV : (z ≫ q) b ∈ V := by
      change q (z b) ∈ V
      rw [hb]
      exact x.property.2
    refine ⟨⟨b, hbV⟩, ?_⟩
    apply (parameterOpen q U V).ι.isOpenEmbedding.injective
    have hh := congrArg (fun f => f ⟨b, hbV⟩) (markToParameter_original q U V z h)
    exact hh.trans hb

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
