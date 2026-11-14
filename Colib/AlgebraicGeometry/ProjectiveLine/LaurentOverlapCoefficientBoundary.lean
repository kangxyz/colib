/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsScalarBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarSupportedBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitComparison
public import Colib.AlgebraicGeometry.Scheme.LaurentInverseCoordinate
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProperties
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentBaseChange
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardOverlapLaurent

/-! # The signed affine overlap boundary for arbitrary perfect coefficients -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local notation "Perf" S => ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X :=
    LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace S)))

local notation "Rst" j => perfectComplexesRestrictOpenImmersion j

set_option backward.isDefEq.respectTransparency false in
private def restrictOpenRangeIso {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    (K : Perf X) :
    (Rst (i.isoOpensRange.inv)).obj ((Rst i).obj K) ≅ (Rst i.opensRange.ι).obj K :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    ((restrictFunctorComp i.isoOpensRange.inv i).symm ≪≫
      restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp i))
    (ComplexShape.up ℤ)).app K.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The polynomial coordinate on the open image is the inverse of the Laurent coordinate. -/
theorem laurentMinus_opensRange_coordinate (R : CommRingCat.{u}) :
    let i := laurentMinus R
    let q := Units.map i.isoOpensRange.inv.appTop.hom.toMonoidHom (laurentCoordinate R)
    i.opensRange.ι.appTop (polynomialCoordinate R) = ↑q⁻¹ := by
  let i := laurentMinus R
  have h := congrArg (fun f => f.appTop (polynomialCoordinate R))
    (Scheme.Hom.isoOpensRange_inv_comp i)
  change i.isoOpensRange.inv.appTop (i.appTop (polynomialCoordinate R)) =
    i.opensRange.ι.appTop (polynomialCoordinate R) at h
  rw [laurentMinus_appTop_coordinate] at h
  exact h.symm

/-- The image of the affine inverse Laurent chart is quasi-compact. -/
theorem laurentMinus_compactSpaceOpensRange (R : CommRingCat.{u}) :
    CompactSpace (laurentMinus R).opensRange.toScheme :=
  isCompact_iff_compactSpace.mp (isCompact_range (laurentMinus R).continuous)

set_option backward.isDefEq.respectTransparency false in
/-- The original Laurent unit on the actual restricted coefficient is preserved by the
canonical identification of the Laurent spectrum with the open image of the inverse chart. -/
theorem laurentMinus_rangeRestrictGlobalUnit (R : CommRingCat.{u})
    (K : Perf(Spec (.of (Polynomial R)))) :
    let i := laurentMinus R
    let q := Units.map i.isoOpensRange.inv.appTop.hom.toMonoidHom (laurentCoordinate R)
    KMap (perfectComplexesRestrictOpenImmersion_isExact i.isoOpensRange.inv) 1
        (perfectGlobalUnitKOneClass _ (laurentCoordinate R) ((Rst i).obj K)) =
      perfectGlobalUnitKOneClass _ q ((Rst i.opensRange.ι).obj K) := by
  let i := laurentMinus R
  dsimp only
  rw [perfectGlobalUnitKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso _ _ (restrictOpenRangeIso i K)

set_option backward.isDefEq.respectTransparency false in
/-- For any perfect polynomial-chart complex, the actual forward Laurent unit
has boundary inverse to the supported cone of the inverse-chart scalar. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/\
    LaurentOverlapCoefficientBoundary.lean:46-60"
  "adaptation" "The forward Laurent class on the actual restricted perfect coefficient"]
theorem laurentMinus_forward_coefficient_boundary (R : CommRingCat.{u})
    (K : Perf(Spec (.of (Polynomial R)))) :
    let i := laurentMinus R
    let j := i.opensRange.ι
    let q := Units.map i.isoOpensRange.inv.appTop.hom.toMonoidHom (laurentCoordinate R)
    let := laurentMinus_compactSpaceOpensRange R
    let hq := laurentMinus_opensRange_coordinate R
    perfectQcqsConnectingHom j 0
      (KMap (perfectComplexesRestrictOpenImmersion_isExact i.isoOpensRange.inv) 1
        (perfectGlobalUnitKOneClass _ (laurentCoordinate R) ((Rst i).obj K))) =
    ((perfectSupportedWaldhausen j).kZeroObjectClass
      ((perfectAcyclicToSupported j).obj
        (perfectOpenScalarCone (polynomialCoordinate R) j q⁻¹ hq K)))⁻¹ := by
  let i := laurentMinus R
  let j := i.opensRange.ι
  let q := Units.map i.isoOpensRange.inv.appTop.hom.toMonoidHom (laurentCoordinate R)
  let := laurentMinus_compactSpaceOpensRange R
  have hq : j.appTop (polynomialCoordinate R) = ↑q⁻¹ := laurentMinus_opensRange_coordinate R
  dsimp only
  rw [laurentMinus_rangeRestrictGlobalUnit]
  have h := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative j 0)
    (perfectScalarForwardKOneClass j K (polynomialCoordinate R) q⁻¹ hq)
  change perfectQcqsConnectingHom j 0 (perfectOpenKRestrict j 1 _) =
    perfectOpenConnectingHom j 0 _ at h
  rw [perfectScalarForwardKOneClass_restrict, perfectOpenConnectingHom_scalarForward,
    perfectGlobalUnitKOneClass_inv, map_inv, inv_eq_iff_eq_inv] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The open image of the inverse Laurent chart is the preimage of the actual standard
overlap in the negative polynomial chart. -/
theorem laurentMinus_opensRange_eq_affineOverlap (R : CommRingCat.{u}) :
    let X : QuasiCompactSchemes.{u} := ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩
    let f := (Relative.polynomialSpecIso R).hom ≫ (standardChartPolynomialIso X 1).inv
    (laurentMinus R).opensRange = f ⁻¹ᵁ chartOverlap X.obj := by
  let X : QuasiCompactSchemes.{u} := ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩
  let A := Relative.polynomialSpecIso R
  let B := Relative.laurentSpecIso R
  let N := standardChartPolynomialIso X 1
  let O := standardOverlapLaurentIso X
  let f := A.hom ≫ N.inv
  let g := B.hom ≫ O.inv
  let i := laurentMinus R
  have h : i ≫ f = g ≫ overlapToNegative X.obj := by
    apply (cancel_mono N.hom).mp
    change (i ≫ A.hom ≫ N.inv) ≫ N.hom = ((B.hom ≫ O.inv) ≫ _) ≫ N.hom
    have hO : overlapToNegative X.obj ≫ N.hom = O.hom ≫ (Relative.minus.app X).hom :=
      overlapToNegative_polynomial X
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hO, Iso.inv_hom_id_assoc]
    exact Relative.polynomialLaurentSpecIso_minus R
  have hr : (i ≫ f).opensRange = chartOverlap X.obj := by
    apply TopologicalSpace.Opens.ext
    change Set.range (i ≫ f) = _
    rw [h]
    change ((g ≫ overlapToNegative X.obj).opensRange : Set (negativeChart X.obj).toScheme) = _
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact congrArg (fun U : (negativeChart X.obj).toScheme.Opens => U.1)
      (chartOverlap X.obj).opensRange_ι
  change i.opensRange = f ⁻¹ᵁ chartOverlap X.obj
  rw [← hr, Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]

end AlgebraicGeometry.Scheme.ProjectiveLine
