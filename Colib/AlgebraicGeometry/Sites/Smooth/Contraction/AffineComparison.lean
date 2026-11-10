/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products

/-!
# Comparison with the original polynomial affine-line projection

The active parameter remains `additiveGroupObject`. The polynomial spectrum is
used only as the original comparison target. The comparison passes through
native relative affine space, retains the actual structure map, and therefore
retains the actual cylinder projection. Constant sections on the comparison
side are literal polynomial evaluation, not unspecified points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The actual native additive base change has the affine-space cartesian square. -/
theorem additiveGroupBaseChange_affineSpace_isPullback (S : Scheme.{u}) :
    IsPullback
      (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S) ≫ additiveGroupAffineSpaceIso.hom)
      (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S))
      (AffineSpace (ULift.{u} Unit) (Spec (.of (ULift.{u} ℤ))) ↘
        Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S) := by
  have h : IsPullback additiveGroupAffineSpaceIso.{u}.hom
      (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (AffineSpace (ULift.{u} Unit) (Spec (.of (ULift.{u} ℤ))) ↘
        Spec (.of (ULift.{u} ℤ))) (𝟙 _) :=
    IsPullback.of_horiz_isIso
      ⟨by simp only [additiveGroupAffineSpaceIso_hom_over, Category.comp_id]⟩
  simpa only [Category.comp_id] using
    (IsPullback.of_hasPullback _ (specULiftZIsTerminal.from S)).paste_horiz h

/-- Base change identifies the existing native line with native relative affine space. -/
def additiveGroupBaseChangeAffineSpaceIso (S : Scheme.{u}) :
    additiveGroupBaseChange S ≅ AffineSpace (ULift.{u} Unit) S :=
  (additiveGroupBaseChange_affineSpace_isPullback S).isoIsPullback _ _
    (AffineSpace.isPullback_map (n := ULift.{u} Unit) (specULiftZIsTerminal.from S))

@[reassoc (attr := simp)]
theorem additiveGroupBaseChangeAffineSpaceIso_hom_over (S : Scheme.{u}) :
    (additiveGroupBaseChangeAffineSpaceIso S).hom ≫
      (AffineSpace (ULift.{u} Unit) S ↘ S) =
      (Scheme.SmoothSite.additiveGroupObject S).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The original univariate polynomial spectrum is compared through its unique variable. -/
def polynomialAffineSpaceIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial R)) ≅ AffineSpace (ULift.{u} Unit) (Spec R) :=
  Scheme.Spec.mapIso
    (MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} Unit) R).symm

@[reassoc (attr := simp)]
theorem polynomialAffineSpaceIso_hom_over (R : CommRingCat.{u}) :
    (polynomialAffineSpaceIso R).hom ≫
      (AffineSpace (ULift.{u} Unit) (Spec R) ↘ Spec R) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  simp only [polynomialAffineSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)).commutes r

/-- This scheme comparison targets exactly the original polynomial spectrum. -/
def nativePolynomialAffineLineIso (R : CommRingCat.{u}) :
    additiveGroupBaseChange (Spec R) ≅ Spec (.of (Polynomial R)) :=
  additiveGroupBaseChangeAffineSpaceIso (Spec R) ≪≫ (polynomialAffineSpaceIso R).symm

@[reassoc (attr := simp)]
theorem nativePolynomialAffineLineIso_hom_over (R : CommRingCat.{u}) :
    (nativePolynomialAffineLineIso R).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      (Scheme.SmoothSite.additiveGroupObject (Spec R)).hom := by
  rw [← polynomialAffineSpaceIso_hom_over]
  simp only [nativePolynomialAffineLineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact additiveGroupBaseChangeAffineSpaceIso_hom_over (Spec R)

namespace Scheme.SmoothSite.Contraction

/-- The original polynomial line is a comparison target, never the active parameter. -/
def polynomialAffineLine (R : CommRingCat.{u}) : SmoothSite (Spec R) := by
  letI : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap R (Polynomial R)).Smooth
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  exact mk (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))

/-- The over-scheme comparison identifies the exact two affine parameters. -/
def affineLinePolynomialIso (R : CommRingCat.{u}) :
    additiveGroupObject (Spec R) ≅ polynomialAffineLine R where
  hom := homMk (nativePolynomialAffineLineIso R).hom
    (nativePolynomialAffineLineIso_hom_over R)
  inv := homMk (nativePolynomialAffineLineIso R).inv (by
    change (nativePolynomialAffineLineIso R).inv ≫
      (additiveGroupObject (Spec R)).hom =
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    rw [← nativePolynomialAffineLineIso_hom_over R]
    exact Iso.inv_hom_id_assoc _ _)
  hom_inv_id := by apply MorphismProperty.Over.Hom.ext; exact Iso.hom_inv_id _
  inv_hom_id := by apply MorphismProperty.Over.Hom.ext; exact Iso.inv_hom_id _

/-- The cylinder comparison is the literal product of the identity with that parameter iso. -/
def affineCylinderPolynomialIso (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    affineLineCylinder.obj X ≅ product X (polynomialAffineLine R) where
  hom := productMap (𝟙 X) (affineLinePolynomialIso R).hom
  inv := productMap (𝟙 X) (affineLinePolynomialIso R).inv
  hom_inv_id := by
    change _ = 𝟙 (product X (additiveGroupObject (Spec R)))
    rw [← productMap_comp]
    simp
  inv_hom_id := by rw [← productMap_comp]; simp

/-- The actual projection comparison, sufficient to identify the original HI predicate. -/
@[reassoc (attr := simp)]
theorem affineCylinderPolynomialIso_hom_projection
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    (affineCylinderPolynomialIso R X).hom ≫ productFst X (polynomialAffineLine R) =
      (projection (additiveGroupObject (Spec R))).app X := by
  simp [affineCylinderPolynomialIso, projection]

/-- Literal polynomial evaluation, as in the original coefficient model. -/
def polynomialAffinePoint (R : CommRingCat.{u}) (a : R) :
    base (Spec R) ⟶ polynomialAffineLine R :=
  homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 R := by
      ext r
      exact Polynomial.eval_C
    rw [h, Spec.map_id])

/-- Constant sections in the original polynomial-spectrum model. -/
def polynomialAffineSection (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) (a : R) :
    X ⟶ product X (polynomialAffineLine R) :=
  productLift (𝟙 X) (toBase X ≫ polynomialAffinePoint R a)

/-- The same evaluation section in native line coordinates. -/
def nativeAffineSection (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) (a : R) :
    X ⟶ affineLineCylinder.obj X :=
  productLift (𝟙 X)
    (toBase X ≫ polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv)

/-- The comparison sends the native-coordinate constant section to literal evaluation. -/
@[reassoc (attr := simp)]
theorem nativeAffineSection_polynomialIso
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) (a : R) :
    nativeAffineSection R X a ≫ (affineCylinderPolynomialIso R X).hom =
      polynomialAffineSection R X a := by
  apply product_hom_ext <;>
    simp [nativeAffineSection, affineCylinderPolynomialIso, polynomialAffineSection]

@[reassoc (attr := simp)]
theorem nativeAffineSection_projection
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) (a : R) :
    nativeAffineSection R X a ≫ (projection (additiveGroupObject (Spec R))).app X = 𝟙 X :=
  productLift_fst _ _

end Scheme.SmoothSite.Contraction

end AlgebraicGeometry
