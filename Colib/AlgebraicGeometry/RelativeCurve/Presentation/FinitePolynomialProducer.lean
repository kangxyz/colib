/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Basic
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.FinitePolynomial
public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.BaseRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.CompactRetainedPrincipalNeighborhood
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.PrescribedCartesian
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.PuncturedCover
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.PrescribedSubquotient
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.BaseBadChart
public import Colib.AlgebraicGeometry.Morphisms.Finite.Open.Pullback

/-! # Original étale presentations constructed from actual finite polynomial coordinates

The inputs are the finite coordinate morphism and an affine smooth open containing
its entire projection fiber. Normalization, full infinity, the common principal
base neighborhood, projective base change and all presentation maps are produced
inside the proof. This is a geometric producer, not a wrapper assuming a retained
presentation or a lifting/correspondence endpoint. Quadratic parameter selection
must separately construct its finite coordinate and whole-fiber hypotheses.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- A genuine finite polynomial map and whole-fiber affine smooth neighborhood
construct the faithful original presentation with both full nonreduced quotients. -/
theorem nonempty_originalEtalePresentation_of_finite_polynomial_coordinates
    (k R B : Type u) [Field k] [CommRing R] [CommRing B] [IsNoetherianRing R]
    (r : Spec (.of R) ⟶ Spec (.of k)) [Smooth r]
    [IsIntegral (Spec (.of B))] [IsNormal (Spec (.of B))]
    (g : Spec (.of B) ⟶ Spec (.of (Polynomial R))) [IsFinite g]
    (P : Spec (.of B))
    (V : (Spec (.of B)).Opens) [IsAffine V.toScheme]
    [SmoothOfRelativeDimension 1
      (V.ι ≫ g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))]
    (hwhole : ∀ x : Spec (.of B),
      (g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) x =
        (g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) P → x ∈ V)
    (I J : Ideal B) (hIJ : I ≤ J)
    [IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))]
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a) (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ)
    [IsFinite (p ∣_ U)] :
    Nonempty (OriginalEtalePresentation k
      (g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ r)
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s P) := by
  let f := g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  let zI := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let zJ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  obtain ⟨N, D, i, π, b, hN, hn, hNoeth, hi, hπ, hb, hbfin, hbrange, _, _, htail⟩ :=
    exists_native_finite_polynomial_compactification k R r g
  let Q := π ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
  have hQ : i ≫ Q = f := htail
  have : IsIntegral N := hN
  have : IsNormal N := hn
  have : IsLocallyNoetherian N := hNoeth
  have : IsOpenImmersion i := hi
  have : IsFinite π := hπ
  have : IsFinite (b ≫ Q) := hbfin
  have : IsFinite (zI ≫ f) := inferInstance
  have : IsFinite (zJ ≫ f) := prescribedSubquotient_finite B I J hIJ f
  have : IsClosedImmersion zI := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion zJ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨t, ht, hWa, hWs, hbT, hWaT, hretain⟩ :=
    exists_compact_retained_principal_neighborhood R i Q f hQ b hbrange V (f P) hwhole zI
  let W := i ''ᵁ V
  let T : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen t
  have hW : (W : Set N) ⊆ Set.range i := by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  have : IsAffine W.toScheme := hWa
  have : SmoothOfRelativeDimension 1 (W.ι ≫ Q) := hWs
  have : IsAffine T.toScheme :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) t).hom
  have hzI : ∀ x : Spec (.of (B ⧸ I)), (zI ≫ f) x ∈ T → i (zI x) ∈ W := hretain
  have hzJ : ∀ x : Spec (.of (B ⧸ J)), (zJ ≫ f) x ∈ T → i (zJ x) ∈ W :=
    prescribedSubquotient_retained B I J hIJ i f T W hzI
  have hxW : i P ∈ W := ⟨P, hwhole P rfl, rfl⟩
  have hxT : Q (i P) ∈ T := by change (i ≫ Q) P ∈ T; rw [hQ]; exact ht
  obtain ⟨hCn, hCnoeth, hCnormal, hπT, _⟩ :=
    finiteProjectiveBaseRestriction_properties 1 π T (i P) hxT
  have : IsNormal (Q ⁻¹ᵁ T).toScheme := hCnormal
  let refinement := retainedBaseToOriginal i Q T W hW
  let j := retainedBaseInclusion Q T W
  let πT := finiteProjectiveBaseRestriction 1 π T
  let tK := T.toScheme.isoSpec.inv ≫ T.ι ≫ r
  let zT := prescribedBaseToRetained i Q f hQ T W hW zJ hzJ
  let sT := retainedEtaleClosedLift i Q f hQ T W hW zJ hzJ p s hs
  let zIN := zI ≫ i
  let dT := coprod.desc (retainedBoundaryInclusion W ∣_ Q ⁻¹ᵁ T) (zIN ∣_ Q ⁻¹ᵁ T)
  have : IsFinite ((zI ≫ i) ≫ Q) := by
    simpa only [Category.assoc, hQ] using (inferInstance : IsFinite (zI ≫ f))
  have : IsClosedImmersion zIN := prescribed_closed_in_compactification i Q zI
  have : IsFinite ((retainedBoundaryInclusion W ≫ Q) ∣_ T) := hbT
  have : IsFinite ((zIN ≫ Q) ∣_ T) := inferInstance
  have hretIN : ∀ x, (zIN ≫ Q) x ∈ T → zIN x ∈ W := by
    simpa only [zIN, Category.assoc, hQ, Scheme.Hom.comp_apply] using hzI
  obtain ⟨hdClosed, hdFinite⟩ := retained_prescribed_boundary_on_base Q W zIN T hretIN
  have : IsFinite (dT ≫ (Q ∣_ T)) := hdFinite
  have : IsFinite (zT ≫ ((W.ι ≫ Q) ∣_ T)) :=
    prescribedBaseToRetained_finite i Q f hQ T W hW zJ hzJ
  have hrbase : refinement ≫ f = ((W.ι ≫ Q) ∣_ T) ≫ T.ι := by
    rw [morphismRestrict_ι, ← hQ, ← Category.assoc refinement, retainedBaseToOriginal_comp]
    simp only [Category.assoc]
  refine ⟨{
    base := Γ(T.toScheme, ⊤)
    base_noetherian := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T.toScheme⟩
    toField := tK
    base_smooth := inferInstance
    target := (retainedBaseOpen Q T W).toScheme
    target_affine := hWaT
    refinement := refinement
    refinement_open := inferInstance
    point := ⟨⟨i P, hxW⟩, hxT⟩
    point_eq := retainedBaseToOriginal_point i Q T W hW P hxW hxT
    compact := (Q ⁻¹ᵁ T).toScheme
    compact_integral := hCn
    compact_noetherian := hCnoeth
    compact_normal := fun x => IsNormal.stalk_normal x
    projectiveMap := πT
    projective_finite := hπT
    inclusion := j
    inclusion_open := inferInstance
    target_smooth := finiteProjectiveBaseRestriction_retained_smooth 1 π T W
    base_compatibility := ?_
    closed := ((zJ ≫ f) ⁻¹ᵁ T).toScheme
    closedToOriginal := ((zJ ≫ f) ⁻¹ᵁ T).ι
    closedInclusion := zT
    closed_cartesian := prescribedBaseToRetained_isPullback i Q f hQ T W hW zJ hzJ
    closed_finite := ?_
    closedLift := sT
    closedLift_original := retainedEtaleClosedLift_fst i Q f hQ T W hW zJ hzJ p s hs
    closedLift_eq := retainedEtaleClosedLift_snd i Q f hQ T W hW zJ hzJ p s hs
    closedLift_closed := retainedEtaleClosedLift_closed i Q f hQ T W hW zJ hzJ p s hs H
    closedLift_cartesian := retainedEtaleClosedLift_isPullback i Q f hQ T W hW zJ hzJ p s hs H
    punctured_disjoint := retainedPunctured_disjoint i Q f hQ T W hW zJ hzJ a ha
    punctured_cover := retainedPunctured_cover i Q f hQ T W hW zJ hzJ a hcover
    boundary := _
    boundaryInclusion := dT
    boundary_closed := hdClosed
    boundary_finite := ?_
    goodOpen := refinement ⁻¹ᵁ U
    good_finite := Scheme.finite_pullback_on_original_chart p refinement U
    bad_cover := ?_ }⟩
  · change refinement ≫ f ≫ r = _
    rw [← Category.assoc, hrbase]
    simp only [πT, tK, Category.assoc, finiteProjectiveBaseRestriction_toSpec_assoc,
      Iso.hom_inv_id_assoc]
    exact (retainedBaseInclusion_projection_assoc Q T W _).symm
  · rw [finiteProjectiveBaseRestriction_toSpec, retainedBaseInclusion_projection_assoc]
    have hcomp : IsFinite ((zT ≫ ((W.ι ≫ Q) ∣_ T)) ≫ T.toScheme.isoSpec.hom) := inferInstance
    exact (Category.assoc zT ((W.ι ≫ Q) ∣_ T) T.toScheme.isoSpec.hom) ▸ hcomp
  · change IsFinite (dT ≫ πT ≫
      (projectiveSpaceOverRing 1 Γ(T.toScheme, ⊤) ↘ Spec Γ(T.toScheme, ⊤)))
    rw [finiteProjectiveBaseRestriction_toSpec, ← Category.assoc]
    infer_instance
  · simpa only [refinement, j, dT, zIN, zI, Scheme.Hom.coe_image,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      using retained_base_bad_chart_cover B I i Q T W hW U hU

end AlgebraicGeometry.Scheme.RelativeCurve
