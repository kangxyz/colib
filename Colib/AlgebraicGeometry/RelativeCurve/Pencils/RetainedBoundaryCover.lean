/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundaryClosed
/-! # The original retained target and whole boundary in the common proper curve -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

section Common
variable {S B C V : Scheme.{u}} (b : B ⟶ S) (π : C ⟶ S) (v : V ⟶ C)

/-- The product of the base source with the retained target over `S`. -/
abbrev retainedProduct := pullback b (v ≫ π)
/-- The product map induced by `v` from the retained product to the ambient product. -/
def retainedProductInclusion : retainedProduct b π v ⟶ pullback b π :=
  (IsPullback.of_hasPullback b π).flip.lift
    (pullback.snd _ _ ≫ v) (pullback.fst _ _) (by rw [Category.assoc, pullback.condition])
@[reassoc (attr := simp)] lemma retainedProductInclusion_fst :
    retainedProductInclusion b π v ≫ pullback.fst b π = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _
@[reassoc (attr := simp)] lemma retainedProductInclusion_snd :
    retainedProductInclusion b π v ≫ pullback.snd b π = pullback.snd _ _ ≫ v :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _
lemma retainedProductInclusion_isPullback :
    IsPullback (pullback.snd b (v ≫ π)) (retainedProductInclusion b π v)
      v (pullback.snd b π) :=
  (IsPullback.of_hasPullback b (v ≫ π)).flip.of_bot' (IsPullback.of_hasPullback b π).flip
instance [IsOpenImmersion v] : IsOpenImmersion (retainedProductInclusion b π v) :=
  MorphismProperty.of_isPullback (retainedProductInclusion_isPullback b π v) inferInstance
lemma retainedProduct_affine [IsAffine S] [IsAffine B] [IsAffine V] :
    IsAffine (retainedProduct b π v) := isAffine_of_isAffineHom (pullback.fst b (v ≫ π))
lemma retainedProduct_smooth [SmoothOfRelativeDimension 1 (v ≫ π)] :
    SmoothOfRelativeDimension 1 (retainedProductInclusion b π v ≫ pullback.fst b π) := by
  rw [retainedProductInclusion_fst]
  exact MorphismProperty.pullback_fst _ _ inferInstance

variable {Y Z D : Scheme.{u}} (j : Y ⟶ C) (α : B ⟶ Y) (s : Z ⟶ Y) (d : D ⟶ C)
lemma commonZeroInclusion_isPullback :
    IsPullback (pullback.snd (commonProjection π j α) (s ≫ j ≫ π))
      (commonZeroInclusion π j α s) (s ≫ j) (pullback.snd (commonProjection π j α) π) := by
  have H : IsPullback (pullback.snd (commonProjection π j α) (s ≫ j ≫ π))
      (pullback.fst _ _) ((s ≫ j) ≫ π) (commonProjection π j α) := by
    simpa only [Category.assoc] using
      (IsPullback.of_hasPullback (commonProjection π j α) (s ≫ j ≫ π)).flip
  convert H.of_bot' (IsPullback.of_hasPullback (commonProjection π j α) π).flip using 1
  apply pullback.hom_ext <;> simp [commonZeroInclusion]

lemma commonBoundary_closed [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
    (hd : Disjoint (Set.range j) (Set.range d)) :
    IsClosedImmersion (commonBoundaryInclusion π j α s d) := by
  have : IsClosedImmersion (commonZeroInclusion π j α s) :=
    MorphismProperty.of_isPullback (commonZeroInclusion_isPullback π j α s) inferInstance
  apply isClosedImmersion_coprodDesc
  apply Set.disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f u)
    (pullback.condition (f := pullback.snd (commonProjection π j α) π) (g := d))
  have h2 := congrArg (fun f => f w) (commonZeroInclusion_isPullback π j α s).w
  have h3 := congrArg (fun t => (pullback.snd (commonProjection π j α) π) t) hw
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩
    (h2.trans (h3.trans h1))

/-- The actual common curve is covered by the original retained target and full boundary. -/
lemma commonBoundary_retained_cover
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ x : commonAmbient π j α,
      x ∈ Set.range (retainedProductInclusion (commonProjection π j α) π v) ∨
        x ∈ Set.range (commonBoundaryInclusion π j α s d) := by
  intro x
  rcases hc ((pullback.snd (commonProjection π j α) π) x) with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (commonProjection π j α) π v) w x hw
    exact Or.inl ⟨t, ht⟩
  · have hx : x ∈ Set.range
        (pullback.fst (pullback.snd (commonProjection π j α) π) d) := by
      rw [Scheme.Pullback.range_fst]
      exact hd
    obtain ⟨w, hw⟩ := hx
    right
    exact ⟨(coprod.inl : commonInfinity π j α d ⟶ commonBoundary π j α s d) w,
      by simpa only [← Scheme.Hom.comp_apply, commonBoundaryInclusion, coprod.inl_desc] using hw⟩
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (commonZeroInclusion_isPullback π j α s) w x hw
    right
    exact ⟨(coprod.inr : commonZero π j α s ⟶ commonBoundary π j α s d) t,
      by simpa only [← Scheme.Hom.comp_apply, commonBoundaryInclusion, coprod.inr_desc] using ht⟩

end Common

section Factors
variable {S X Y A Z C D V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C) (v : V ⟶ C)

lemma lambdaBoundary_retained_cover
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ x : (pullback (j ≫ π) π : Scheme.{u}),
      x ∈ Set.range (retainedProductInclusion (j ≫ π) π v) ∨
        x ∈ Set.range (fullGraphBoundaryMap π j s d) := by
  intro x
  rcases hc ((pullback.snd (j ≫ π) π) x) with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (j ≫ π) π v) w x hw
    exact Or.inl ⟨t, ht⟩
  · have hx : x ∈ Set.range (pullback.fst (pullback.snd (j ≫ π) π) d) := by
      rw [Scheme.Pullback.range_fst]
      exact hd
    obtain ⟨w, hw⟩ := hx
    exact Or.inr ⟨(coprod.inl : pullback (pullback.snd (j ≫ π) π) d ⟶
      pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) w, by
      simpa only [← Scheme.Hom.comp_apply, fullGraphBoundaryMap,
        coprod.inl_desc, infinityProductMap] using hw⟩
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (markedProductMap_isPullback π j s).flip w x hw
    exact Or.inr ⟨(coprod.inr : pullback (j ≫ π) (s ≫ j ≫ π) ⟶
      pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) t, by
      simpa only [← Scheme.Hom.comp_apply, fullGraphBoundaryMap,
        coprod.inr_desc] using ht⟩

lemma psiBoundary_retained_cover
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ x : (pullback (a ≫ q) π : Scheme.{u}),
      x ∈ Set.range (retainedProductInclusion (a ≫ q) π v) ∨
        x ∈ Set.range (psiBoundaryInclusion q π j p hq a z s hs d) := by
  intro x
  rcases hc ((pullback.snd (a ≫ q) π) x) with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (a ≫ q) π v) w x hw
    exact Or.inl ⟨t, ht⟩
  · have hx : x ∈ Set.range (pullback.fst (pullback.snd (a ≫ q) π) d) := by
      rw [Scheme.Pullback.range_fst]
      exact hd
    obtain ⟨w, hw⟩ := hx
    exact Or.inr ⟨(coprod.inl : pullback (pullback.snd (a ≫ q) π) d ⟶
      pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) w, by
      simpa only [← Scheme.Hom.comp_apply, psiBoundaryInclusion, coprod.inl_desc] using hw⟩
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (psiZeroInclusion_isPullback q π j p hq a z s hs) w x hw
    exact Or.inr ⟨(coprod.inr : pullback (a ≫ q) (z ≫ q) ⟶
      pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) t, by
      simpa only [← Scheme.Hom.comp_apply, psiBoundaryInclusion, coprod.inr_desc] using ht⟩

end Factors

end AlgebraicGeometry.Scheme.RelativeCurvePencil
