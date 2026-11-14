/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateBoundaryFormula
public import Colib.AlgebraicGeometry.Modules.PerfectRankOne
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarSupportedBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitComparison

/-! # The rank-one projective coordinate cone in K-zero -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local notation "W" S => RingedSpace.perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace S))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Compare the actual cone K-map and the two tensor orders on the same complexes.
private theorem coordinateCone_KMap_forget (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : (W X.obj).K n) :
    let j := (standardChart X.obj 0).ι
    perfectSupportedKMap j n
      (KMap (perfectNegativeTwistCoordinateCone_exact X.obj 0) n
        (KMap (projectiveLineFirstSummand_exact X.obj) n a)) =
      projectiveLineKMap X.obj n (a, a⁻¹) := by
  let Y := projectiveSpaceOver 1 X.obj
  let j := (standardChart X.obj 0).ι
  let L := twistOver 1 X.obj (-1)
  let : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) L :=
    let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := Y.ringCatSheaf) L 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y _
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  let z := KMap (projectiveLineFirstSummand_exact X.obj) n a
  let α := perfectNegativeTwistCoordinate X.obj 0
  let hC := perfectNegativeTwistCoordinateCone_exact X.obj 0
  have h := perfectSupportedTransformationCone_KMap_forget j α
    (perfectTensorRight_waldhausenExact L) (IsExact.id (W Y).cof (W Y).weq)
    (perfectNegativeTwistCoordinate_openWeak X.obj 0) hC n z
  have htwist : KMap (perfectTensorRight_waldhausenExact L) n z =
      KMap (projectiveLineSecondSummand_exact X.obj) n a := by
    change (KMap (perfectTensorRight_waldhausenExact L) n).comp
      (KMap (projectiveLineFirstSummand_exact X.obj) n) a = _
    rw [KMap_comp_KMap]
    exact DFunLike.congr_fun (KMap_eq_of_iso
      ((projectiveLineFirstSummand_exact X.obj).comp (perfectTensorRight_waldhausenExact L))
      (projectiveLineSecondSummand_exact X.obj)
      (Functor.isoWhiskerLeft (projectiveLineFirstSummand X.obj) (perfectTensorLeftRightIso L).symm)
      n) a
  rw [KMap_id, MonoidHom.id_apply, htwist] at h
  dsimp only
  rw [projectiveLineKMap_apply, map_inv]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Elaborating the native object classes unfolds the support and forgetful functors.
/-- Forgetting support on the actual homogeneous coordinate cone of the pulled-back rank-one
object gives the difference of the two projective summands in degree zero. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeTautologicalConeClass.lean"
  "adaptation" "Actual native coordinate cone without the separate affine projective model"]
theorem perfectNegativeTwistCoordinateCone_rankOne_class (X : QuasiCompactSchemes.{u}) :
    let Y := projectiveSpaceOver 1 X.obj
    let j := (standardChart X.obj 0).ι
    let F := perfectSupportedTransformationCone j (perfectNegativeTwistCoordinate X.obj 0)
      (perfectNegativeTwistCoordinate_openWeak X.obj 0)
    let K := rankOnePerfectComplex X.obj
    let a := (W X.obj).kZeroObjectClass K
    (W Y).kZeroObjectClass
      ((perfectSupportedInclusion j).obj (F.obj ((projectiveLineFirstSummand X.obj).obj K))) =
      projectiveLineKMap X.obj 0 (a, a⁻¹) := by
  have h := coordinateCone_KMap_forget X 0
    ((W X.obj).kZeroObjectClass (rankOnePerfectComplex X.obj))
  dsimp only at h ⊢
  rw [KMap_kZeroObjectClass, KMap_kZeroObjectClass] at h
  change KMap (perfectSupportedInclusion_isExact (standardChart X.obj 0).ι) 0 _ = _ at h
  rw [KMap_kZeroObjectClass] at h
  exact h

private def rankOneFlatPullbackIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Flat f] :
    (perfectFlatPullback f).obj (rankOnePerfectComplex Z) ≅ rankOnePerfectComplex Y :=
  ObjectProperty.isoMk (P := RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))
    (((HomologicalComplex.singleMapHomologicalComplex (pullback f) (.up ℤ) 0).app
      (SheafOfModules.unit Z.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor Y.Modules 0).mapIso
        (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- The scalar and excision comparisons unfold the two exact restriction functors.
/-- The actual forward Laurent unit on the structure complex has projective boundary with
coordinates `(e⁻¹,e)` for the base's rank-one class `e`. -/
theorem connectingHom_forwardCoordinateUnit_rankOne (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let U := (j ⁻¹ᵁ T).toScheme
    let a := (W X.obj).kZeroObjectClass (rankOnePerfectComplex X.obj)
    PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) 0
      (perfectGlobalUnitKOneClass U (overlapCoordinateUnit X) (rankOnePerfectComplex U)) =
      projectiveLineKMap X.obj 0 (a⁻¹, a) := by
  let Y := projectiveSpaceOver 1 X.obj
  let j := (negativeChart X.obj).ι
  let V := (negativeChart X.obj).toScheme
  let T := positiveChart X.obj
  let U := (j ⁻¹ᵁ T).toScheme
  let i := (j ⁻¹ᵁ T).ι
  let r := negativeChartCoordinate X
  let q : (Γ(U, ⊤))ˣ := overlapCoordinateUnit X
  have hq : i.appTop r = (q⁻¹).val := negativeChartCoordinate_restrict X
  let K := rankOnePerfectComplex X.obj
  let a := (W X.obj).kZeroObjectClass K
  let z := KMap (projectiveLineFirstSummand_exact X.obj) 0 a
  let P := perfectComplexesRestrictOpenImmersion j
  let α := perfectNegativeTwistCoordinate X.obj 0
  let e := negativeChartPerfectFrame X
  let k := Functor.leftUnitor P
  let hC := perfectNegativeTwistCoordinateCone_exact X.obj 0
  have h : Functor.whiskerRight α P ≫ k.hom =
      e.hom ≫ Functor.whiskerLeft P (perfectGlobalScalar V r) := by
    apply NatTrans.ext
    funext M
    change P.map (α.app M) ≫ 𝟙 _ = (P.map
      ((perfectNegativeTwistCoordinate X.obj 1).app M) ≫ 𝟙 _) ≫ _
    simp only [Category.comp_id]
    exact perfectNegativeTwistCoordinate_restrict_zero X M
  have hrank : KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 z =
      (W V).kZeroObjectClass (rankOnePerfectComplex V) := by
    dsimp only [z, a]
    rw [KMap_kZeroObjectClass, KMap_kZeroObjectClass]
    exact (W V).kZeroObjectClass_iso
      (P.mapIso (rankOneFlatPullbackIso (projectiveSpaceOver 1 X.obj ↘ X.obj)) ≪≫
        rankOnePerfectComplexRestrictIso j)
  have hc := DFunLike.congr_fun (perfectSupportedKRestrict_comp_transformationCone j T r q⁻¹ hq
    α (perfectNegativeTwistCoordinate_openWeak X.obj 0) hC e k h 0) z
  change perfectSupportedKRestrict j T 0 (KMap hC 0 z) =
    perfectSupportedScalarConeKMap i r q⁻¹ hq 0
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 z) at hc
  rw [hrank] at hc
  have hscalar := perfectOpenConnectingHom_scalarForward i (rankOnePerfectComplex V) r q⁻¹ hq
  have hs := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative i 0)
    (perfectScalarForwardKOneClass i (rankOnePerfectComplex V) r q⁻¹ hq)
  change perfectQcqsConnectingHom i 0 (perfectOpenKRestrict i 1 _) =
    perfectOpenConnectingHom i 0 _ at hs
  rw [perfectScalarForwardKOneClass_restrict_rankOne, hscalar] at hs
  have hcone : perfectQcqsConnectingHom i 0
      (perfectGlobalUnitKOneClass U q⁻¹ (rankOnePerfectComplex U)) =
      perfectSupportedKRestrict j T 0 (KMap hC 0 z) := by
    rw [hc, hs]
    exact (KMap_kZeroObjectClass
      (perfectSupportedScalarConeFunctor_waldhausenExact i r q⁻¹ hq)
      (rankOnePerfectComplex V)).symm
  have hlower : PerfectMayerVietoris.lowerBoundary j T (standardChart_cover X.obj) 0
      (perfectGlobalUnitKOneClass U q⁻¹ (rankOnePerfectComplex U)) = KMap hC 0 z := by
    apply (perfectSupportedExcisionKEquiv j T (standardChart_cover X.obj) 0).injective
    let E := perfectSupportedExcisionKEquiv j T (standardChart_cover X.obj) 0
    change E (E.symm
      (perfectQcqsConnectingHom i 0 _)) = perfectSupportedKRestrict j T 0 _
    rwa [MulEquiv.apply_symm_apply]
  have hboundary : PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) 0
      (perfectGlobalUnitKOneClass U q⁻¹ (rankOnePerfectComplex U)) =
      projectiveLineKMap X.obj 0 (a, a⁻¹) := by
    change perfectSupportedKMap T.ι 0
      (PerfectMayerVietoris.lowerBoundary j T (standardChart_cover X.obj) 0 _) = _
    rw [hlower]
    exact coordinateCone_KMap_forget X 0 a
  rw [perfectGlobalUnitKOneClass_inv, map_inv] at hboundary
  have hinv := congrArg Inv.inv hboundary
  simpa only [inv_inv, ← map_inv, Prod.inv_mk] using hinv

end AlgebraicGeometry.Scheme.ProjectiveLine
