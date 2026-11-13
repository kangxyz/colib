/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.PolynomialBaseChange
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.RestrictMarkedSquare
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Coordinates on the original affine marked refinement

The literal coefficient restriction of the presented line is compared to
the polynomial line over the section ring of its base open. The étale
source, closed mark, puncture and their Cartesian square retain their
original restricted domains.

Adapted from the affine refinement and complement comparisons under
Motivic/Aglib/AlgebraicGeometry/Normalization/Compactification/RelativeAffineLine
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme

section

variable (R : Type u) [CommRing R]
  {T : Scheme.{u}} (e : T ≅ Spec (.of (Polynomial R)))
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- The actual target-open restriction followed by the canonical native line iso. -/
def affineRefinedTargetIso :
    ((e.hom ≫ polynomialProjection (.of R)) ⁻¹ᵁ O).toScheme ≅
      Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  asIso (e.hom ∣_ (polynomialProjection (.of R) ⁻¹ᵁ O)) ≪≫ (polynomialLineAffineOpenIso R O).symm

@[reassoc]
theorem affineRefinedTargetIso_coordinate :
    (affineRefinedTargetIso R e O).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (affineOpenCoefficientMap R O))) =
      ((e.hom ≫ polynomialProjection (.of R)) ⁻¹ᵁ O).ι ≫ e.hom := by
  simp only [affineRefinedTargetIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, polynomialLineAffineOpenIso_inv_coordinate, morphismRestrict_ι]
  rfl

@[reassoc]
theorem affineRefinedTargetIso_projection :
    (affineRefinedTargetIso R e O).hom ≫ polynomialProjection (.of Γ(O.toScheme, ⊤)) =
      ((e.hom ≫ polynomialProjection (.of R)) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
  simp only [affineRefinedTargetIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, polynomialLineAffineOpenIso_inv_projection, Iso.hom_inv_id_assoc,
    morphismRestrict_ι, morphismRestrict_ι_assoc]
  rfl

instance affineRefinedTarget_affine :
    IsAffine ((e.hom ≫ polynomialProjection (.of R)) ⁻¹ᵁ O).toScheme :=
  .of_isIso (affineRefinedTargetIso R e O).hom

/-- A genuinely affine original open member stays affine under this coefficient restriction. -/
theorem affineRefinedOpen_affine {A : Scheme.{u}} [IsAffine A] (i : A ⟶ T) :
    IsAffine ((i ≫ e.hom ≫ polynomialProjection (.of R)) ⁻¹ᵁ O).toScheme := by
  let : IsAffine T := .of_isIso e.hom
  exact (show IsAffineOpen ((e.hom ≫ polynomialProjection (.of R)) ⁻¹ᵁ O) from
    affineRefinedTarget_affine R e O).preimage i

end

section

variable (R : Type u) [CommRing R] {T Y Z : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ polynomialProjection (.of R) = q)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- The target-open comparison retains all original source domains. -/
def originalAffineRefinedTargetIso : (q ⁻¹ᵁ O).toScheme ≅
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  T.isoOfEq (by rw [hq]) ≪≫ affineRefinedTargetIso R e O

@[reassoc]
theorem originalAffineRefinedTargetIso_coordinate :
    (originalAffineRefinedTargetIso R e q hq O).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (affineOpenCoefficientMap R O))) =
      (q ⁻¹ᵁ O).ι ≫ e.hom := by
  simp only [originalAffineRefinedTargetIso, Iso.trans_hom, Category.assoc,
    affineRefinedTargetIso_coordinate]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι]

@[reassoc]
theorem originalAffineRefinedTargetIso_projection :
    (originalAffineRefinedTargetIso R e q hq O).hom ≫
      polynomialProjection (.of Γ(O.toScheme, ⊤)) = (q ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
  simp only [originalAffineRefinedTargetIso, Iso.trans_hom, Category.assoc,
    affineRefinedTargetIso_projection, Iso.hom_inv_id_assoc, morphismRestrict_ι]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι, hq]

/-- The polynomial line over the actual restricted coefficient ring is the
original target pullback, with its literal map into that target. -/
theorem originalAffineRefinedTarget_isPullback :
    IsPullback ((originalAffineRefinedTargetIso R e q hq O).inv ≫ (q ⁻¹ᵁ O).ι)
      (polynomialProjection (.of Γ(O.toScheme, ⊤))) q (O.toScheme.isoSpec.inv ≫ O.ι) := by
  refine (isPullback_morphismRestrict q O).flip.of_iso
    (originalAffineRefinedTargetIso R e q hq O) (Iso.refl _)
    O.toScheme.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact (originalAffineRefinedTargetIso_projection R e q hq O).symm
  · simp
  · simp

variable (p : Y ⟶ T) (W : Y.Opens) (hW : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ O))

/-- Native map on the literal affine open produced from the original representative. -/
def originalAffineRefinedNativeMap :
    W.toScheme ⟶ Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  p.resLE (q ⁻¹ᵁ O) W hW ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativeMap_etale [Etale p] :
    Etale (originalAffineRefinedNativeMap R e q hq O p W hW) := by
  unfold originalAffineRefinedNativeMap
  infer_instance

@[reassoc]
theorem originalAffineRefinedNativeMap_coordinate :
    originalAffineRefinedNativeMap R e q hq O p W hW ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (affineOpenCoefficientMap R O))) =
      W.ι ≫ p ≫ e.hom := by
  simp only [originalAffineRefinedNativeMap, Category.assoc,
    originalAffineRefinedTargetIso_coordinate]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

variable (z : Z ⟶ T)

/-- The native marked map has the original full marked restriction as its domain. -/
def originalAffineRefinedNativeMarked : ((z ≫ q) ⁻¹ᵁ O).toScheme ⟶
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (z ∣_ (q ⁻¹ᵁ O)) ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativeMarked_closed [IsClosedImmersion z] :
    IsClosedImmersion (originalAffineRefinedNativeMarked R e q hq O z) := by
  unfold originalAffineRefinedNativeMarked
  infer_instance

instance originalAffineRefinedNativeMarked_finite [IsFinite (z ≫ q)] :
    IsFinite (originalAffineRefinedNativeMarked R e q hq O z ≫
      polynomialProjection (.of Γ(O.toScheme, ⊤))) := by
  have he : originalAffineRefinedNativeMarked R e q hq O z ≫
      polynomialProjection (.of Γ(O.toScheme, ⊤)) = ((z ≫ q) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
    apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
    simp only [originalAffineRefinedNativeMarked, Category.assoc,
      originalAffineRefinedTargetIso_projection, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, morphismRestrict_ι_assoc]
    rfl
  rw [he]
  infer_instance

/-- The original marked lift t and its full square are unchanged. -/
theorem originalAffineRefinedNativeMarked_isPullback
    (t : ((z ≫ q) ⁻¹ᵁ O).toScheme ⟶ W.toScheme)
    (H : IsPullback t (𝟙 _) (p.resLE (q ⁻¹ᵁ O) W hW) (z ∣_ (q ⁻¹ᵁ O))) :
    IsPullback t (𝟙 _) (originalAffineRefinedNativeMap R e q hq O p W hW)
      (originalAffineRefinedNativeMarked R e q hq O z) :=
  H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (originalAffineRefinedTargetIso R e q hq O)
    (by simp) (by simp) (by simp [originalAffineRefinedNativeMap])
    (by simp [originalAffineRefinedNativeMarked])

end

/-- Reindexing the ambient scheme preserves the exact full complement. -/
theorem range_comp_iso_complement {X X' A Z : Scheme.{u}}
    (e : X ≅ X') (a : A ⟶ X) (z : Z ⟶ X)
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (z ≫ e.hom) = (Set.range (a ≫ e.hom))ᶜ := by
  have mem (Y : Scheme.{u}) (g : Y ⟶ X) (x : X') :
      x ∈ Set.range (g ≫ e.hom) ↔ e.inv x ∈ Set.range g := by
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      change g y = (g ≫ e.hom ≫ e.inv) y
      simp
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change e.hom (g y) = x
      rw [hy]
      change (e.inv ≫ e.hom) x = x
      simp
  ext x
  rw [Set.mem_compl_iff, mem, mem, hz]
  rfl

variable (R : Type u) [CommRing R] {T A Z : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ polynomialProjection (.of R) = q)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : A ⟶ T) (z : Z ⟶ T)

/-- The original puncture is restricted only over the same coefficient open. -/
def originalAffineRefinedNativePuncture : ((a ≫ q) ⁻¹ᵁ O).toScheme ⟶
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (a ∣_ (q ⁻¹ᵁ O)) ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativePuncture_open [IsOpenImmersion a] :
    IsOpenImmersion (originalAffineRefinedNativePuncture R e q hq O a) := by
  unfold originalAffineRefinedNativePuncture
  infer_instance

/-- The first native reindexing keeps the exact original complement. -/
theorem originalAffineRefinedNative_complement
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (originalAffineRefinedNativeMarked R e q hq O z) =
      (Set.range (originalAffineRefinedNativePuncture R e q hq O a))ᶜ :=
  range_comp_iso_complement (originalAffineRefinedTargetIso R e q hq O)
    (a ∣_ (q ⁻¹ᵁ O)) (z ∣_ (q ⁻¹ᵁ O))
    (range_morphismRestrict_complement a z (q ⁻¹ᵁ O) hz)

include hq in
/-- Affineness of the original puncture survives this same restriction. -/
theorem originalAffineRefinedNativePuncture_affine [IsAffine A] :
    IsAffine ((a ≫ q) ⁻¹ᵁ O).toScheme := by
  rw [← hq]
  exact affineRefinedOpen_affine R e O a

end AlgebraicGeometry.Scheme
