/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeBaseTorus

/-! # The whole polynomial puncture and the existing native torus

The complete zero complement, transported by the existing line comparison,
constructs the isomorphism. The positive Laurent open is retained exactly.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- Complement comparison for the literal whole line, with no puncture shrink. -/
theorem exists_polynomialPuncture_comparison :
    ∃ t : etalePullback (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _) ⟶
        torusCylinder.obj (affineSite k R),
      IsPullback t
        (etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))
        (Contraction.openInclusion.app (affineSite k R))
        (lineCylinderIso (k := k) (R := R)).hom := by
  have H₁ : IsPullback (lineZero (k := k) (R := R)).left (𝟙 _)
      (𝟙 _) (lineZero (k := k) (R := R)).left :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have H₂ : IsPullback (lineZero (k := k) (R := R)).left (𝟙 _)
      (lineCylinderIso (k := k) (R := R)).hom.left
      (nativeAffineSection (.of k) (affineSite k R) 0).left :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [Category.id_comp, MorphismProperty.Comma.comp_left] using
        congrArg (fun f => f.left) (lineZero_cylinder (k := k) (R := R))⟩
  exact (exists_native_cartier_puncture_comparison (.of k)
    polynomialPunctureInclusion (𝟙 _) lineCylinderIso.hom lineZero
    lineZero.left (𝟙 _) H₁ H₂ (range_lineZero (k := k) (R := R))).2

/-- The actual comparison of the pullback puncture with the multiplicative cylinder. -/
def polynomialPunctureComparison :=
  (exists_polynomialPuncture_comparison (k := k) (R := R)).choose

private theorem polynomialPunctureComparison_isPullback :
    IsPullback (polynomialPunctureComparison (k := k) (R := R))
      (etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))
      (Contraction.openInclusion.app (affineSite k R))
      (lineCylinderIso (k := k) (R := R)).hom :=
  (exists_polynomialPuncture_comparison (k := k) (R := R)).choose_spec

instance polynomialPunctureComparison_isIso :
    IsIso (polynomialPunctureComparison (k := k) (R := R)) :=
  (polynomialPunctureComparison_isPullback (k := k) (R := R)).isIso_fst_of_isIso

instance polynomialPuncturePullbackFst_isIso : IsIso
    (etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _)) :=
  (show IsPullback
    (etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))
    (etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))
    polynomialPunctureInclusion (𝟙 _) from
      IsPullback.of_isLimit (etalePullbackConeIsLimit _ _)).isIso_fst_of_isIso

/-- The entire original D(X) is the entire existing multiplicative cylinder. -/
def _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.puncturedProductIso :
    openSite (k := k) (Polynomial.X : Polynomial R) ≅
        torusCylinder.obj (affineSite k R) :=
  (asIso (etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))).symm ≪≫
    asIso (polynomialPunctureComparison (k := k) (R := R))

/-- This comparison preserves the original polynomial open and native positive open. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.puncturedProductIso_open :
    (puncturedProductIso (k := k) (R := R)).hom ≫
      Contraction.openInclusion.app (affineSite k R) =
        polynomialPunctureInclusion ≫ (lineCylinderIso (k := k) (R := R)).hom := by
  apply (cancel_epi
    (etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _))).mp
  have h := (polynomialPunctureComparison_isPullback (k := k) (R := R)).w
  have hc := (etalePullbackCone
    (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _)).condition
  simp only [Category.comp_id] at hc
  simp only [puncturedProductIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hproj : etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _) ≫
      polynomialPunctureInclusion =
      etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R)) (𝟙 _) := hc
  rwa [hproj]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
