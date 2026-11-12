/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality
public import Colib.AlgebraicGeometry.AffineLine.Open.AffineLineZeroNeighborhoodBaseShrink

/-! # Literal evaluation zero in the unchanged native affine cylinder

The base-open comparison is the existing whole-line comparison. Both its zero
section and its original coefficient map are identified, including the full
Cartesian zero scheme. No new affine parameter or point model is introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The full original polynomial zero, as a morphism in Sm/k. -/
def lineZero : affineSite k R ⟶ lineSite (k := k) (R := R) :=
  homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) (by
    change Spec.map _ ≫ (Spec.map _ ≫ _) = _
    rw [← Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by ext r; simp
    rw [h, Spec.map_id, Category.id_comp]
    rfl)

@[reassoc (attr := simp)] theorem lineZero_projection :
    (lineZero (k := k) (R := R)).left ≫ polynomialProjection (.of R) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by ext r; simp
  rw [h, Spec.map_id]
  rfl

@[reassoc] theorem lineZero_polynomialProduct :
    lineZero (k := k) (R := R) ≫ linePolynomialProductIso.hom =
      polynomialAffineSection (.of k) (affineSite k R) 0 := by
  apply product_hom_ext
  · simp only [Category.assoc, linePolynomialProductIso_projection,
      polynomialAffineSection, productLift_fst]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by ext r; simp
    rw [h, Spec.map_id]
  · simp only [Category.assoc, polynomialAffineSection, productLift_snd]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
    rw [ambientIso_snd]
    exact polynomial_zero_scalar_naturality (algebraMap k R)

/-- The selected coordinate is literally native zero, not an unspecified section. -/
@[reassoc] theorem lineZero_cylinder :
    lineZero (k := k) (R := R) ≫ lineCylinderIso.hom =
      nativeAffineSection (.of k) (affineSite k R) 0 := by
  apply (cancel_mono (affineCylinderPolynomialIso (.of k) (affineSite k R)).hom).mp
  simp only [lineCylinderIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, nativeAffineSection_polynomialIso]
  exact lineZero_polynomialProduct

/-- The whole native cylinder map of an actual base-open inclusion is open. -/
instance lineBaseOpen_cylinderMap_isOpenImmersion (V : (affineSite k R).left.Opens) :
    IsOpenImmersion
      (affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V)).left := by
  let e := lineBaseOpenCylinderIso (k := k) V
  let e' := lineCylinderIso (k := k) (R := R)
  let j := SmoothSite.openInclusion (lineSite (k := k) (R := R))
    (polynomialProjection (.of R) ⁻¹ᵁ V)
  let : IsIso e.inv.left := inferInstanceAs
    (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso e).inv)
  let : IsIso e'.hom.left := inferInstanceAs
    (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso e').hom)
  let : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (polynomialProjection (.of R) ⁻¹ᵁ V).ι)
  have h := e.eq_inv_comp.mpr
    (lineBaseOpenCylinderIso_comp (k := k) V)
  rw [congrArg (fun f => f.left) h]
  exact inferInstanceAs (IsOpenImmersion (e.inv.left ≫ j.left ≫ e'.hom.left))

/-- The original zero of the whole base open, factored through its full line. -/
def lineBaseOpenZero (V : (affineSite k R).left.Opens) :
    (opensFunctor (affineSite k R)).obj V ⟶
      (opensFunctor (lineSite (k := k) (R := R))).obj
        (polynomialProjection (.of R) ⁻¹ᵁ V) :=
  homMk (IsOpenImmersion.lift (polynomialProjection (.of R) ⁻¹ᵁ V).ι
    (V.ι ≫ (lineZero (k := k) (R := R)).left) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨(V.ι ≫ (lineZero (k := k) (R := R)).left) x, ?_⟩, rfl⟩
      change (V.ι ≫ (lineZero (k := k) (R := R)).left ≫ polynomialProjection (.of R)) x ∈ V
      rw [lineZero_projection, Category.comp_id]
      exact x.property)) (by
        change IsOpenImmersion.lift _ _ _ ≫ (_ ≫ _) = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
          MorphismProperty.Over.w]
        rfl)

@[reassoc (attr := simp)] theorem lineBaseOpenZero_original
    (V : (affineSite k R).left.Opens) :
    lineBaseOpenZero (k := k) V ≫
      SmoothSite.openInclusion (lineSite (k := k) (R := R)) (polynomialProjection (.of R) ⁻¹ᵁ V) =
        SmoothSite.openInclusion (affineSite k R) V ≫ lineZero := by
  apply MorphismProperty.Over.Hom.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The base-open line comparison retains its entire original zero section. -/
@[reassoc] theorem lineBaseOpenZero_cylinder (V : (affineSite k R).left.Opens) :
    lineBaseOpenZero (k := k) V ≫ (lineBaseOpenCylinderIso (k := k) V).hom =
      nativeAffineSection (.of k) ((opensFunctor (affineSite k R)).obj V) 0 := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono
    (affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V)).left).mp
  have h : (lineBaseOpenZero (k := k) V ≫
      (lineBaseOpenCylinderIso (k := k) V).hom) ≫
        affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V) =
      nativeAffineSection (.of k) ((opensFunctor (affineSite k R)).obj V) 0 ≫
        affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V) := by
    simp only [Category.assoc, lineBaseOpenCylinderIso_comp,
      lineBaseOpenZero_original_assoc, lineZero_cylinder,
      nativeAffineSection_naturality]
  exact congrArg (fun f => f.left) h

/-- This comparison preserves the full zero fiber, not only its support. -/
theorem lineBaseOpenZero_isPullback (V : (affineSite k R).left.Opens) :
    IsPullback (lineBaseOpenZero (k := k) V).left V.ι
      (polynomialProjection (.of R) ⁻¹ᵁ V).ι (lineZero (k := k) (R := R)).left := by
  have hw : (lineBaseOpenZero (k := k) V).left ≫
      (polynomialProjection (.of R) ⁻¹ᵁ V).ι =
      V.ι ≫ (lineZero (k := k) (R := R)).left :=
    congrArg (fun f => f.left) (lineBaseOpenZero_original (k := k) V)
  apply IsOpenImmersion.isPullback _ _ _ _ hw.symm
  ext x
  simp only [Scheme.Opens.opensRange_ι]
  change polynomialProjection (.of R) ((lineZero (k := k) (R := R)).left x) ∈ V ↔ x ∈ V
  have hp := congrArg (fun f => f x) (lineZero_projection (k := k) (R := R))
  change polynomialProjection (.of R) ((lineZero (k := k) (R := R)).left x) = x at hp
  rw [hp]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
