/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Original coefficient and base-open maps in native cylinder coordinates -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Affine/LineOpenMaps.lean`, blob
`071f40f3b886b314f34363eaf07e821c2cd01ccf`.
The active affine cylinder remains the existing native additive group object.
The polynomial spectrum is only an explicit comparison target.
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
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

/-- The actual coefficient restriction is the original cylinder map. -/
@[reassoc] theorem linePolynomialProductIso_naturality (φ : R →ₐ[k] S) :
    lineMap φ ≫ (linePolynomialProductIso (k := k) (R := R)).hom =
      (linePolynomialProductIso (k := k) (R := S)).hom ≫
        productMap (affineMorphism φ) (𝟙 (Contraction.polynomialAffineLine (.of k))) := by
  apply product_hom_ext
  · simp only [Category.assoc, productMap_fst,
      linePolynomialProductIso_projection_assoc, linePolynomialProductIso_projection]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom)) ≫
        polynomialProjection (.of R) =
      polynomialProjection (.of S) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Polynomial.map_C φ.toRingHom
  · simp only [Category.assoc, productMap_snd,
      Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom)) ≫
        (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _ =
      (ambientIso (algebraMap k S)).hom ≫ pullback.snd _ _
    rw [ambientIso_snd, ambientIso_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp

omit [Algebra.Smooth k R] in
/-- Restricting only the base leaves the entire original affine-line product. -/
theorem lineBaseOpen_isPullback (V : (Spec (.of R)).Opens) :
    IsPullback (polynomialProjection (.of R) ∣_ V)
      ((polynomialProjection (.of R) ⁻¹ᵁ V).ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))))
      (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (polynomialProjection (.of k)) :=
  (isPullback_morphismRestrict (polynomialProjection (.of R)) V).paste_vert
    (ambient_isPullback (algebraMap k R))

/-- The original whole-line base open is the actual cylinder over that base open. -/
def lineBaseOpenPolynomialProductIso (V : (Spec (.of R)).Opens) :
    (opensFunctor (lineSite (k := k) (R := R))).obj
      (polynomialProjection (.of R) ⁻¹ᵁ V) ≅
        product ((opensFunctor (affineSite k R)).obj V)
          (Contraction.polynomialAffineLine (.of k)) :=
  MorphismProperty.Over.isoMk (lineBaseOpen_isPullback (k := k) V).isoPullback (by
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
      (pullback.fst _ _ ≫ (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))) = _
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rfl)

/-- The whole-line comparison preserves the literal original base-open restriction. -/
@[reassoc] theorem lineBaseOpenPolynomialProductIso_comp (V : (Spec (.of R)).Opens) :
    (lineBaseOpenPolynomialProductIso (k := k) V).hom ≫
        productMap (openInclusion (affineSite k R) V)
          (𝟙 (Contraction.polynomialAffineLine (.of k))) =
      openInclusion (lineSite (k := k) (R := R))
        (polynomialProjection (.of R) ⁻¹ᵁ V) ≫
          (linePolynomialProductIso (k := k) (R := R)).hom := by
  apply product_hom_ext
  · simp only [Category.assoc, productMap_fst, linePolynomialProductIso_projection]
    apply MorphismProperty.Over.Hom.ext
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
        pullback.fst _ _ ≫ V.ι = _
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact morphismRestrict_ι _ _
  · simp only [Category.assoc, productMap_snd,
      Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
        pullback.snd _ _ =
      (polynomialProjection (.of R) ⁻¹ᵁ V).ι ≫
        (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _
    rw [IsPullback.isoPullback_hom_snd, ambientIso_snd]


/-- Coefficient restriction agrees with the actual native cylinder morphism. -/
@[reassoc] theorem lineCylinderIso_naturality (φ : R →ₐ[k] S) :
    lineMap φ ≫ (lineCylinderIso (k := k) (R := R)).hom =
      (lineCylinderIso (k := k) (R := S)).hom ≫
        Contraction.affineLineCylinder.map (affineMorphism φ) := by
  simp only [lineCylinderIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, linePolynomialProductIso_naturality, Category.assoc,
    Contraction.affineCylinderPolynomialIso_inv_naturality, ← Category.assoc]

/-- The full inverse image of a base open is its unchanged native cylinder. -/
def lineBaseOpenCylinderIso (V : (Spec (.of R)).Opens) :
    (opensFunctor (lineSite (k := k) (R := R))).obj
      (polynomialProjection (.of R) ⁻¹ᵁ V) ≅
        Contraction.affineLineCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  lineBaseOpenPolynomialProductIso V ≪≫
    (Contraction.affineCylinderPolynomialIso (.of k)
      ((opensFunctor (affineSite k R)).obj V)).symm

/-- The native comparison preserves the entire original base-open inclusion. -/
@[reassoc] theorem lineBaseOpenCylinderIso_comp (V : (Spec (.of R)).Opens) :
    (lineBaseOpenCylinderIso (k := k) V).hom ≫
        Contraction.affineLineCylinder.map (openInclusion (affineSite k R) V) =
      openInclusion (lineSite (k := k) (R := R))
        (polynomialProjection (.of R) ⁻¹ᵁ V) ≫
          (lineCylinderIso (k := k) (R := R)).hom := by
  simp only [lineBaseOpenCylinderIso, lineCylinderIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ← Contraction.affineCylinderPolynomialIso_inv_naturality,
    ← Category.assoc, lineBaseOpenPolynomialProductIso_comp, Category.assoc]

open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
attribute [local instance] sectionsAlgebra

/-- Affine coordinates preserve projection to the original base object. -/
@[reassoc] theorem affineLineIso_projection
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (affineLineIso X).hom ≫
        (Contraction.projection (additiveGroupObject (Spec (.of k)))).app X =
      homMk (polynomialProjection (.of Γ(X.left, ⊤))) rfl ≫ (affineIso X).hom := by
  change ((lineCylinderIso (k := k) (R := Γ(X.left, ⊤))).hom ≫
    Contraction.affineLineCylinder.map (affineIso X).hom) ≫
      (Contraction.projection (additiveGroupObject (Spec (.of k)))).app X = _
  rw [Category.assoc, (Contraction.projection
    (additiveGroupObject (Spec (.of k)))).naturality, ← Category.assoc,
    lineCylinderIso_projection, Functor.id_map]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
