/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.CoordinateRankOne
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateUnitProjection
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseSpecSquare
public import Colib.AlgebraicGeometry.KTheory.PerfectPolynomialUnitComparison

/-! # The forward rank-one Laurent class in the affine Bass row -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local notation "W" X => RingedSpace.perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X))

set_option quotPrecheck false in
local notation "affineBase" R => (⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩ :
  QuasiCompactSchemes)

set_option quotPrecheck false in
local notation "affineLaurentIso" R =>
  (show Spec (.of (LaurentPolynomial R)) ≅ (Relative.laurentFunctor.obj (affineBase R)).obj
    from Relative.laurentSpecIso R)

set_option backward.isDefEq.respectTransparency false in
private theorem affineLaurentCoordinate_inv (R : CommRingCat.{u}) :
    let X := affineBase R
    Units.map ((affineLaurentIso R).inv.appTop.hom.toMonoidHom) (laurentCoordinate R) =
      relativeLaurentCoordinateUnit X := by
  let X := affineBase R
  let B : Spec (.of (LaurentPolynomial R)) ≅ (Relative.laurentFunctor.obj X).obj :=
    Relative.laurentSpecIso R
  have h : Units.map B.hom.appTop.hom.toMonoidHom (relativeLaurentCoordinateUnit X) =
      laurentCoordinate R := IntegerSpec.nativeLaurentUnit_spec R
  rw [← h]
  apply Units.ext
  have hid := congrArg (fun f => f.appTop) B.inv_hom_id
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hid
  exact ConcreteCategory.congr_hom hid (↑(relativeLaurentCoordinateUnit X))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The affine pullback and open restriction elaborate with the canonical exact functors.
/-- The genuine projective connecting map in the affine Bass row gives the coordinates
`(e⁻¹,e)` on the actual forward Laurent unit of the structure complex. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/LaurentRankOneBoundary.lean:30-42"
  "adaptation" "Actual forward Laurent-unit class and signed native projective coordinates"]
theorem affineConnectingCoefficients_forward_rankOne (R : CommRingCat.{u}) :
    let X := affineBase R
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let e := (W (Spec R)).kZeroObjectClass (rankOnePerfectComplex (Spec R))
    (projectiveLineKEquiv X.obj 0).symm
      (PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) 0
        (perfectKPullback ((standardOverlapLaurentIso X).hom ≫
          (affineLaurentIso R).inv) 1
          (perfectGlobalUnitKOneClass _ (laurentCoordinate R)
            (rankOnePerfectComplex (Spec (.of (LaurentPolynomial R))))))) = (e⁻¹, e) := by
  let X := affineBase R
  let B : Spec (.of (LaurentPolynomial R)) ≅ (Relative.laurentFunctor.obj X).obj :=
    Relative.laurentSpecIso R
  let A := standardOverlapLaurentIso X
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let U := (j ⁻¹ᵁ T).toScheme
  let e := (W (Spec R)).kZeroObjectClass (rankOnePerfectComplex (Spec R))
  let f : U ⟶ Spec (.of (LaurentPolynomial R)) := A.hom ≫ B.inv
  let _ : IsIso f := by dsimp only [f]; infer_instance
  have hq : Units.map f.appTop.hom.toMonoidHom (laurentCoordinate R) =
      overlapCoordinateUnit X := by
    rw [← relativeLaurentCoordinateUnit_restrict X, ← affineLaurentCoordinate_inv R]
    apply Units.ext
    rfl
  change (projectiveLineKEquiv X.obj 0).symm
    (PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) 0
      (perfectKPullback f 1 (perfectGlobalUnitKOneClass _ (laurentCoordinate R)
        (rankOnePerfectComplex (Spec (.of (LaurentPolynomial R))))))) = (e⁻¹, e)
  rw [perfectKPullback_eq_restrict, perfectGlobalUnitKOneClass_restrict_rankOne, hq]
  have h := connectingHom_forwardCoordinateUnit_rankOne X
  dsimp only at h
  rw [h]
  change (projectiveLineKEquiv X.obj 0).symm (projectiveLineKEquiv X.obj 0 (e⁻¹, e)) = _
  exact (projectiveLineKEquiv X.obj 0).symm_apply_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The original signed Bass boundary takes the actual forward Laurent rank-one unit to
the inverse rank-one class of the coefficient ring. -/
@[colib_tag "COL-1291"]
theorem affinePositiveBassBoundary_forward_rankOne (R : CommRingCat.{u}) :
    let X := affineBase R
    positiveBassBoundary X 0
        (perfectKPullback (affineLaurentIso R).inv 1
          (perfectGlobalUnitKOneClass _ (laurentCoordinate R)
            (rankOnePerfectComplex (Spec (.of (LaurentPolynomial R)))))) =
      ((W (Spec R)).kZeroObjectClass (rankOnePerfectComplex (Spec R)))⁻¹ := by
  have h := congrArg Prod.fst (affineConnectingCoefficients_forward_rankOne R)
  dsimp only at h
  rw [perfectKPullback_comp, MonoidHom.comp_apply, perfectKPullback_eq_flatPullback] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The independent forward polynomial scalar class has the same terminal sign after its
actual open restriction and rebase to the affine Laurent scheme. -/
@[colib_tag "COL-1291"]
theorem affinePositiveBassBoundary_polynomialScalarForward_rankOne (R : CommRingCat.{u}) :
    let X := affineBase R
    positiveBassBoundary X 0
        (perfectKPullback (affineLaurentIso R).inv 1
          (perfectOpenKRestrict (laurentToPolynomial R) 1
            (perfectScalarForwardKOneClass (laurentToPolynomial R)
              (rankOnePerfectComplex (Spec (.of (Polynomial R)))) (polynomialCoordinate R)
              (laurentCoordinate R) (laurentToPolynomial_appTop_coordinate R)))) =
      ((W (Spec R)).kZeroObjectClass (rankOnePerfectComplex (Spec R)))⁻¹ := by
  rw [polynomialScalarForwardKOneClass_restrict_rankOne]
  exact affinePositiveBassBoundary_forward_rankOne R

end AlgebraicGeometry.Scheme.ProjectiveLine
