/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeBaseTorus
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedSmoothSites
public import Colib.AlgebraicGeometry.Morphisms.Smooth.PolynomialProjection

/-! # Exact native cylinder coordinates on the U = top refined sources

The generic pencil's actual second source is a pullback, not an open chosen to
be isomorphic to a torus. Its full parameter and its two projections are
transported to the existing native affine and multiplicative cylinders.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
local notation "q" => polynomialProjection (CommRingCat.of R)
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k R))
local notation "W" => parameterOpen q ⊤ V
set_option quotPrecheck false in
local notation "L" => q ⁻¹ᵁ V
set_option quotPrecheck false in
local notation "D" => PolynomialOpenQuotient.principalOpen (Polynomial.X : Polynomial R)
local instance : IsAffine (D).toScheme := IsAffineOpen.Spec_basicOpen _
local instance : SmoothOfRelativeDimension 1 q :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R
local instance : IsAffine (W).toScheme := by
  change IsAffineOpen W
  have h : IsAffineOpen L := (show IsAffineOpen V from ‹IsAffine V.toScheme›).preimage q
  simpa only [parameterOpen, top_inf_eq] using h
local instance : Smooth (parameterProjection q ⊤ V) :=
  SmoothOfRelativeDimension.smooth 1 _

local instance : QuasiCompact (parameterProjection q ⊤ V ≫ V.ι ≫ b) :=
  quasiCompact_of_compactSpace _

/-- The entire polynomial parameter after a base-only refinement. -/
abbrev wholeParameterSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (parameterProjection q ⊤ V ≫ V.ι ≫ b)

/-- The explicit equality of open images, preserving their original inclusions. -/
def wholeParameterOpenIso : (W).toScheme ≅ (L).toScheme :=
  IsOpenImmersion.isoOfRangeEq (W).ι (L).ι (by
    simp only [Scheme.Opens.range_ι, parameterOpen, top_inf_eq])

omit [IsAffine V.toScheme] in
@[reassoc (attr := simp)] theorem wholeParameterOpenIso_original :
    (wholeParameterOpenIso V).hom ≫ (L).ι = (W).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The source of this comparison is the pencil's original parameter object. -/
def wholeParameterSiteIso : wholeParameterSite (k := k) V ≅
    (opensFunctor (lineSite (k := k) (R := R))).obj L :=
  MorphismProperty.Over.isoMk (wholeParameterOpenIso V) (by
    change (wholeParameterOpenIso V).hom ≫ ((L).ι ≫ (q ≫ b)) =
      parameterProjection q ⊤ V ≫ V.ι ≫ b
    rw [wholeParameterOpenIso_original_assoc, ← Category.assoc, ← parameterProjection_base,
      Category.assoc])

/-- The full parameter is the unchanged native affine cylinder over exactly V. -/
def wholeParameterCylinderIso : wholeParameterSite (k := k) V ≅
    Contraction.affineLineCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  wholeParameterSiteIso (k := k) V ≪≫ lineBaseOpenCylinderIso (k := k) V

/-- The complete zero of V in the original parameter W. -/
def wholeParameterZero : (opensFunctor (affineSite k R)).obj V ⟶
    wholeParameterSite (k := k) V :=
  lineBaseOpenZero (k := k) V ≫ (wholeParameterSiteIso (k := k) V).inv

@[reassoc] theorem wholeParameterZero_cylinder :
    wholeParameterZero (k := k) V ≫ (wholeParameterCylinderIso (k := k) V).hom =
      Contraction.nativeAffineSection (.of k) ((opensFunctor (affineSite k R)).obj V) 0 := by
  simp only [wholeParameterZero, wholeParameterCylinderIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc, lineBaseOpenZero_cylinder]

@[reassoc] theorem wholeParameterZero_original :
    (wholeParameterZero (k := k) V).left ≫ (W).ι =
      V.ι ≫ (lineZero (k := k) (R := R)).left := by
  have hZero : (wholeParameterZero (k := k) V).left =
      (lineBaseOpenZero (k := k) V).left ≫ (wholeParameterOpenIso V).inv := rfl
  calc
    _ = ((lineBaseOpenZero (k := k) V).left ≫ (wholeParameterOpenIso V).inv) ≫
        ((wholeParameterOpenIso V).hom ≫ (L).ι) :=
      congrArg₂ (· ≫ ·) hZero (wholeParameterOpenIso_original V).symm
    _ = (lineBaseOpenZero (k := k) V).left ≫ (L).ι := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := congrArg (fun f => f.left) (lineBaseOpenZero_original (k := k) V)

/-- The original polynomial ambient map, including the original coefficient map. -/
@[reassoc] theorem wholeParameterCylinderIso_original :
    (wholeParameterCylinderIso (k := k) V).hom.left ≫
      (Contraction.affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V)).left =
        (W).ι ≫ (lineCylinderIso (k := k) (R := R)).hom.left := by
  have hBase := congrArg (fun f => f.left) (lineBaseOpenCylinderIso_comp (k := k) V)
  change (lineBaseOpenCylinderIso (k := k) V).hom.left ≫
      (Contraction.affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V)).left =
      (L).ι ≫ (lineCylinderIso (k := k) (R := R)).hom.left at hBase
  change ((wholeParameterOpenIso V).hom ≫
    (lineBaseOpenCylinderIso (k := k) V).hom.left) ≫ _ = _
  rw [Category.assoc, hBase, ← Category.assoc, wholeParameterOpenIso_original]

/-- The actual second projection, now into the full parameter site. -/
def wholeSecondParameter : refinedSecondSite b q ⊤ V (D).ι ⟶
    wholeParameterSite (k := k) V :=
  SmoothSite.homMk (secondMap q ⊤ V (D).ι) (by
    change secondMap q ⊤ V (D).ι ≫ (parameterProjection q ⊤ V ≫ V.ι ≫ b) =
      (secondMap q ⊤ V (D).ι ≫ parameterProjection q ⊤ V) ≫ (V.ι ≫ b)
    exact (Category.assoc _ _ _).symm)

omit [IsAffine V.toScheme] in
/-- The full second source is Cartesian over the unchanged polynomial puncture. -/
theorem wholeSecondBasePullback :
    IsPullback (pullback.fst (D).ι (W).ι)
      (pullback.snd (D).ι (W).ι ≫ (wholeParameterOpenIso V).hom) (D).ι (L).ι := by
  apply (IsPullback.of_hasPullback (D).ι (W).ι).of_iso
    (Iso.refl _) (Iso.refl _) (wholeParameterOpenIso V) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp

/-- Both original projections determine the comparison to the full puncture model. -/
def wholeSecondBaseIso : refinedSecondSite b q ⊤ V (D).ι ≅ wholeBasePuncture (k := k) V :=
  MorphismProperty.Over.isoMk (wholeSecondBasePullback V).isoPullback (by
    change (wholeSecondBasePullback V).isoPullback.hom ≫
      (pullback.snd (D).ι (L).ι ≫ ((L).ι ≫ (q ≫ b))) =
        (secondMap q ⊤ V (D).ι ≫ parameterProjection q ⊤ V) ≫ (V.ι ≫ b)
    rw [← Category.assoc, IsPullback.isoPullback_hom_snd]
    simp only [Category.assoc, wholeParameterOpenIso_original_assoc, secondMap]
    have hBase : (W).ι ≫ (q ≫ b) = parameterProjection q ⊤ V ≫ (V.ι ≫ b) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ b) (parameterProjection_base q ⊤ V)).symm.trans
          (Category.assoc _ _ _))
    exact congrArg (pullback.snd (D).ι (W).ι ≫ ·) hBase)

@[reassoc] theorem wholeSecondBaseIso_parameter :
    (wholeSecondBaseIso (k := k) V).hom ≫
      etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R))
        (SmoothSite.openInclusion _ _) =
    wholeSecondParameter (k := k) V ≫ (wholeParameterSiteIso (k := k) V).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (wholeSecondBasePullback V).isoPullback.hom ≫ pullback.snd (D).ι (L).ι =
    pullback.snd (D).ι (W).ι ≫ (wholeParameterOpenIso V).hom
  exact (wholeSecondBasePullback V).isoPullback_hom_snd

/-- The pencil's actual second source is the whole native torus over V. -/
def wholeSecondTorusIso : refinedSecondSite b q ⊤ V (D).ι ≅
    Contraction.torusCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  wholeSecondBaseIso (k := k) V ≪≫ wholeBasePunctureTorusIso (k := k) V

/-- The precise native open commutes with the original second projection. -/
@[reassoc] theorem wholeSecondTorusIso_open :
    (wholeSecondTorusIso (k := k) V).hom ≫
      Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V) =
    wholeSecondParameter (k := k) V ≫ (wholeParameterCylinderIso (k := k) V).hom := by
  simp only [wholeSecondTorusIso, wholeParameterCylinderIso, Iso.trans_hom, Category.assoc,
    wholeBasePunctureTorusIso_open, wholeSecondBaseIso_parameter_assoc]

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
