/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.OriginalOverlapLifting
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.SecondOriginalRestriction
public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.OriginalPointLifting
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.MarkedAffineComposition

/-! # Affine marked torus corrections on the original neighborhood

The two signed identities compose on the actual étale pullback of their
affine ambient schemes. The original ambient maps, full zero marking, and
whole torus square are preserved.

Adapted from `AffineCombinedCorrection` and `CombinedCorrection` at Motivic
revision `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem affineCorrection_cylinderMap_open
    {k : Type u} [Field k] {B C : SmoothSite (Spec (.of k))}
    (v : B ⟶ C) [IsOpenImmersion v.left] :
    IsOpenImmersion (Contraction.affineLineCylinder.map v).left := by
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion v.left))
    (inferInstanceAs (IsOpenImmersion (𝟙 (additiveGroupObject (Spec (.of k))).left)))
    (MorphismProperty.Over.w v).symm (Category.id_comp _).symm

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] (R : Type u) [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (w : Spec (.of R))
  (e : OriginalEtalePresentation k (lineSite (k := k) (R := R)).hom p.left
    (polynomialPunctureInclusion (k := k) (R := R)).left z s (polynomialZero R w))

local instance : IsAffine (lineSite (k := k) (R := R)).left :=
  inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
local instance : IsAffine
    ((opensFunctor (lineSite (k := k) (R := R))).obj (puncture R)).left :=
  IsAffineOpen.Spec_basicOpen _
local instance (A : Type u) [CommRing A] : IsAffine (puncture A).toScheme :=
  IsAffineOpen.Spec_basicOpen _
local instance (A : Type u) [CommRing A] (T : (Spec (.of A)).Opens)
    [IsAffine T.toScheme] : IsAffine (parameterOpen (coordinateLineProjection A) ⊤ T).toScheme := by
  change IsAffineOpen (parameterOpen (coordinateLineProjection A) ⊤ T)
  have h : IsAffineOpen (coordinateLineProjection A ⁻¹ᵁ T) :=
    (show IsAffineOpen T from ‹IsAffine T.toScheme›).preimage _
  simpa only [parameterOpen, top_inf_eq] using h
local notation "a₁" => polynomialPunctureInclusion (k := k) (R := R)
local notation "x" => polynomialZero R w

section ScalarAssembly
variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme] [IsAffine (parameterOpen e.curveProjection U V).toScheme]
local notation "Q₁" => retainedCorrectionSquare p a₁ z s x e U V
local notation "φ₁" => retainedOverlapToOriginal p a₁ z s x e U V
local notation "η₁" => retainedEtaleToOriginal p a₁ z s x e U V
local notation "u₁" => retainedToOriginal e U V

set_option maxHeartbeats 700000 in
-- The native coefficient, first source and marked pullback use constructed smooth-site objects.
/-- Internal assembly of the already constructed signed identities, with their
literal maps. Its correction inputs are discharged by the public producer below. -/
private theorem exists_scalar_affine_torus_neighborhood_lifting
    (P : PresheafWithTransfers.{u + 1} k)
    (s₀ : Spec (.of R) ⟶ Y.left) (hs₀ : s₀ ≫ p.left = polynomialZero R)
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ (Q₁).f₁₂ (Q₁).f₁₃)
    {S : Type u} [CommRing S] [Algebra k S] [Algebra.Smooth k S]
    (f : R →ₐ[k] S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsAffine (secondOriginalOpen p z s x e U V f).toScheme]
    (V₂ : (Spec (.of S)).Opens) [IsAffine V₂.toScheme]
    (hzero : Set.range (polynomialZero S) ⊆ secondOriginalOpen p z s x e U V f)
    (w' : Spec (.of S)) (hw' : Spec.map (CommRingCat.ofHom f.toRingHom) w' = w)
    (hwV₂ : w' ∈ V₂)
    (h₂ : P.HasRestrictionDifferenceLifting
      (secondOriginalRestriction p z s x e U V f V₂)
      (wholeZeroBeta (k := k) S (secondOriginalOpen p z s x e U V f) V₂)
      (refinedAlpha (k := k) (Spec.map (CommRingCat.ofHom (algebraMap k S)))
        (coordinateLineProjection S) ⊤ V₂ (ZeroNeighborhood.compactProjection S)
        ((secondOriginalOpen p z s x e U V f).ι ≫ chart S)
        (secondOriginalOpen p z s x e U V f).ι
        (inclusion_projection S (secondOriginalOpen p z s x e U V f)) (puncture S).ι)) :
    ∃ (B : SmoothSite (Spec (.of k))) (v : B ⟶ affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ Contraction.affineLineCylinder.obj B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale q.left ∧
        η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom =
          q ≫ Contraction.affineLineCylinder.map v ∧
        ζ ≫ q.left = (Contraction.nativeAffineSection (.of k) B 0).left ∧
        ζ ≫ η.left = v.left ≫ s₀ ∧
        ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E)
          (β : O ⟶ Contraction.torusCylinder.obj B)
          (φ : O ⟶ etalePullback p a₁),
          IsPullback β.left α.left (Contraction.openInclusion.app B).left q.left ∧
          φ ≫ etalePullbackFst p a₁ = α ≫ η ∧
          P.HasRestrictionDifferenceLifting φ β α := by
  let O₂ := secondOriginalOpen p z s x e U V f
  let B := (opensFunctor (affineSite k S)).obj V₂
  let v : B ⟶ affineSite k R := SmoothSite.openInclusion (affineSite k S) V₂ ≫ affineMorphism f
  let q₂ := wholeZeroFirstCylinder (k := k) S O₂ V₂
  let : IsOpenImmersion q₂.left :=
    inferInstanceAs (IsOpenImmersion (wholeZeroFirstCylinder (k := k) S O₂ V₂).left)
  let : Etale q₂.left := inferInstance
  let ζ₂ := wholeZeroFirstSection (k := k) S O₂ V₂ hzero
  let m := secondOriginalAmbient p z s x e U V f V₂
  have hz : ζ₂ ≫ m.left ≫ u₁ = (v.left ≫ s₀) ≫ p.left := by
    change ζ₂ ≫ m.left ≫ u₁ =
      ((V₂.ι ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) ≫ s₀) ≫ p.left
    rw [Category.assoc, hs₀, Category.assoc]
    exact secondOriginalAmbient_zero (k := k) p z s x e U V f V₂ hzero
  let : IsAffine (Q₁).X₄.left := inferInstanceAs
    (IsAffine (parameterOpen e.curveProjection U V).toScheme)
  let : IsAffine ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsAffine Y.left)
  let : IsAffine ((𝟭 Scheme).obj (lineSite (k := k) (R := R)).left) :=
    inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
  let : IsAffineHom p.left := isAffineHom_of_isAffine p.left
  let : IsAffine (Q₁).X₃.left := IsAffine.of_isIso
    (retainedEtale_original_isPullback p a₁ z s x e U V).isoPullback.hom
  have hT₂ : IsAffine (pullback O₂.ι
      (parameterOpen (coordinateLineProjection S) ⊤ V₂).ι) := inferInstance
  let : IsAffine (refinedFirstSite (k := k) (Spec.map (CommRingCat.ofHom (algebraMap k S)))
      (coordinateLineProjection S) ⊤ V₂ (ZeroNeighborhood.compactProjection S)
      (O₂.ι ≫ chart S) O₂.ι (inclusion_projection S O₂)).left := hT₂
  obtain ⟨E, η, q, ζ, hE, hq, hbase, hζq, hζη, O, α, β, φ, H, hφ, hL⟩ :=
    PresheafWithTransfers.HasRestrictionDifferenceLifting.comp_on_affine_marked_etale_pullback
      P h₁ h₂ (Q₁).f₂₄ (Q₁).f₃₄
      (retainedCorrectionSquare_isPullback p a₁ z s x e U V) m
      (secondOriginalRestriction_ambient p z s x e U V f V₂)
      (Contraction.openInclusion.app B) q₂ (wholeZeroCylinder_isPullback (k := k) S O₂ V₂)
      p η₁ u₁ (retainedEtale_original_isPullback p a₁ z s x e U V)
      (lineCylinderIso (k := k) (R := R)).hom.left
      (Contraction.affineLineCylinder.map v).left
      (secondOriginalCylinder_original p z s x e U V f V₂).symm
      (etalePullbackFst p a₁) (retainedOverlapToOriginal_etale p a₁ z s x e U V)
      ζ₂ (v.left ≫ s₀) (Contraction.nativeAffineSection (.of k) B 0).left hz
      (wholeZeroFirstSection_cylinder (k := k) S O₂ V₂ hzero)
  have hv : IsOpenImmersion v.left := by
    change IsOpenImmersion (V₂.ι ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
    infer_instance
  refine ⟨B, v, (show IsAffine V₂.toScheme from inferInstance), hv, ⟨⟨w', hwV₂⟩, hw'⟩,
    E, η, q, ζ, hE, hq, ?_, hζq,
    hζη, O, α, β, φ, H, hφ, hL⟩
  exact MorphismProperty.Over.Hom.ext hbase

/-- The second identity is obtained from a true original coefficient localization,
then restricted to the unchanged first puncture before marked composition. -/
private theorem exists_retained_affine_torus_neighborhood_lifting
    (hw : x ∈ retainedOriginalOpen e U V)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left) (hs₀ : s₀ ≫ p.left = polynomialZero R)
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ (Q₁).f₁₂ (Q₁).f₁₃) :
    ∃ (B : SmoothSite (Spec (.of k))) (v : B ⟶ affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ Contraction.affineLineCylinder.obj B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale q.left ∧
        η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom =
          q ≫ Contraction.affineLineCylinder.map v ∧
        ζ ≫ q.left = (Contraction.nativeAffineSection (.of k) B 0).left ∧
        ζ ≫ η.left = v.left ≫ s₀ ∧
        ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E)
          (β : O ⟶ Contraction.torusCylinder.obj B)
          (φ : O ⟶ etalePullback p a₁),
          IsPullback β.left α.left (Contraction.openInclusion.app B).left q.left ∧
          φ ≫ etalePullbackFst p a₁ = α ≫ η ∧
          P.HasRestrictionDifferenceLifting φ β α := by
  let : IsAffine (retainedOriginalOpen e U V).toScheme := retainedOriginalOpen_affine e U V
  obtain ⟨r, _hr, hO₂, hzero, w', hw', V₂, hV₂, hwV₂, h₂⟩ :=
    exists_zeroPoint_native_torus_lifting (k := k) R (retainedOriginalOpen e U V) P hP w hw
  let S := Localization.Away r
  let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let : IsAffine (secondOriginalOpen p z s x e U V f).toScheme := hO₂
  let : IsAffine V₂.toScheme := hV₂
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
    infer_instance
  have h₂' := PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P h₂
    (secondOriginalTarget p z s x e U V f V₂)
  exact exists_scalar_affine_torus_neighborhood_lifting R p z s w e U V P s₀ hs₀ h₁
    f V₂ hzero w' hw' hwV₂ h₂'
end ScalarAssembly

include e in
/-- Construct both signed corrections and assemble them on one actual original
etale neighborhood. All base, zero, torus and original-overlap maps are retained. -/
theorem exists_original_affine_torus_neighborhood_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left) (hs₀ : s₀ ≫ p.left = polynomialZero R) :
    ∃ (B : SmoothSite (Spec (.of k))) (v : B ⟶ affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ Contraction.affineLineCylinder.obj B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale η.left ∧ Etale q.left ∧
        η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom =
          q ≫ Contraction.affineLineCylinder.map v ∧
        ζ ≫ q.left = (Contraction.nativeAffineSection (.of k) B 0).left ∧
        ζ ≫ η.left = v.left ≫ s₀ ∧
        ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E)
          (β : O ⟶ Contraction.torusCylinder.obj B)
          (φ : O ⟶ etalePullback p a₁),
          IsPullback β.left α.left (Contraction.openInclusion.app B).left q.left ∧
          φ ≫ etalePullbackFst p a₁ = α ≫ η ∧
          P.HasRestrictionDifferenceLifting φ β α := by
  obtain ⟨U, _hU, hxU, V, hV, hxV, _hmark, hW, h₁⟩ :=
    exists_original_overlap_lifting p a₁ z s x e P hP
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen e.curveProjection U V).toScheme := hW
  have hw : x ∈ retainedOriginalOpen e U V := point_mem_retainedOriginalOpen e U V hxU hxV
  obtain ⟨B, v, hB, hv, hwB, E, η, q, ζ, hE, hq, hbase, hζq, hζη, hrest⟩ :=
    exists_retained_affine_torus_neighborhood_lifting R p z s w e U V hw P hP s₀ hs₀ h₁
  let : IsOpenImmersion v.left := hv
  let : Etale q.left := hq
  let : IsOpenImmersion (Contraction.affineLineCylinder.map v).left :=
    SmoothSite.affineCorrection_cylinderMap_open v
  have hcomp : Etale (η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom).left := by
    rw [hbase]
    exact inferInstanceAs (Etale (q.left ≫ (Contraction.affineLineCylinder.map v).left))
  let : IsIso (lineCylinderIso (k := k) (R := R)).hom.left :=
    inferInstanceAs (IsIso ((forgetScheme (Spec (.of k))).mapIso
      (lineCylinderIso (k := k) (R := R))).hom)
  let : Etale (η.left ≫ (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left)) := hcomp
  have hη : Etale η.left := Etale.of_comp η.left
    (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left)
  exact ⟨B, v, hB, hv, hwB, E, η, q, ζ, hE, hη, hq, hbase, hζq, hζη, hrest⟩

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
