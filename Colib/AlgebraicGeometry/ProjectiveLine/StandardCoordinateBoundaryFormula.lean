/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardPerfectCoordinateScalar
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardPerfectCoordinateCone
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisScalarCone
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwoSummands

/-! # The original Laurent unit boundary in projective-line coordinates -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local instance (S : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFree
      (R := (projectiveSpaceOver 1 S).ringCatSheaf) (twistOver 1 S (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (projectiveSpaceOver 1 S).ringCatSheaf) (twistOver 1 S (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme
      (projectiveSpaceOver 1 S) _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the native perfect negative twist to the negative chart, the actual frame
`T₁` identifies it with ordinary restriction. -/
def negativeChartPerfectFrame (X : QuasiCompactSchemes.{u}) :
    Modules.perfectTensorRight (twistOver 1 X.obj (-1)) ⋙
        perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι ≅
      perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι := by
  let R := perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι
  let α := Functor.whiskerRight (perfectNegativeTwistCoordinate X.obj 1) R ≫
    (Functor.leftUnitor R).hom
  let : ∀ K, IsIso (α.app K) := fun K => by
    let f := (perfectNegativeTwistCoordinate X.obj 1).app K
    let : IsIso (R.map f) := isIso_restrict_perfectNegativeTwistCoordinate X.obj 1 K
    change IsIso (R.map f ≫ 𝟙 _)
    infer_instance
  let : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- A standard chart over a quasi-separated base is quasi-separated. -/
instance (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    QuasiSeparatedSpace (negativeChart S).toScheme :=
  quasiSeparatedSpace_of_quasiSeparated (negativeChart S).ι

/-- The two-open intersection over a qcqs base is compact as a scheme. -/
instance (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :
    CompactSpace (chartOverlap S).toScheme :=
  isCompact_iff_compactSpace.mp (chartOverlap_isCompact S)

instance (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :
    CompactSpace (((negativeChart S).ι ⁻¹ᵁ positiveChart S).toScheme) :=
  inferInstanceAs (CompactSpace (chartOverlap S).toScheme)

local notation "PL" S => projectiveSpaceOver 1 S
local notation "WK" S => RingedSpace.perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace S))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Elaborating the original support-excision boundary unfolds the two exact restriction functors.
/-- The native Mayer–Vietoris connecting homomorphism of the original inverse Laurent unit
has its two original projective-line summands, with signs `(a,a⁻¹)`. -/
theorem connectingHom_inverseCoordinateUnit (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (a : (WK(X.obj)).K n) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let q := (overlapCoordinateUnit X)⁻¹
    PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
      (originalKSelfTrackOperation (WK((negativeChart X.obj).toScheme))
        (WK((j ⁻¹ᵁ T).toScheme)) (perfectFlatUnitHomotopy (j ⁻¹ᵁ T).ι q)
        n (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
          (KMap (projectiveLineFirstSummand_exact X.obj) n a))) =
      projectiveLineKMap X.obj n (a, a⁻¹) := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let R := perfectComplexesRestrictOpenImmersion j
  let L := twistOver 1 X.obj (-1)
  let α := perfectNegativeTwistCoordinate X.obj 0
  let z := KMap (projectiveLineFirstSummand_exact X.obj) n a
  let e := negativeChartPerfectFrame X
  let k := Functor.leftUnitor R
  have h : Functor.whiskerRight α R ≫ k.hom =
      e.hom ≫ Functor.whiskerLeft R
        (perfectGlobalScalar (negativeChart X.obj).toScheme (negativeChartCoordinate X)) := by
    apply NatTrans.ext
    funext K
    change R.map (α.app K) ≫ 𝟙 _ = (R.map
      ((perfectNegativeTwistCoordinate X.obj 1).app K) ≫ 𝟙 _) ≫ _
    simp only [Category.comp_id]
    exact perfectNegativeTwistCoordinate_restrict_zero X K
  have hα : ∀ K, (perfectOpenWeakWaldhausen T.ι).weq (α.app K) :=
    perfectNegativeTwistCoordinate_openWeak X.obj 0
  have hc := PerfectMayerVietoris.connectingHom_scalarUnit_of_cone j T
    (standardChart_cover X.obj) α hα
    (perfectNegativeTwistCoordinateCone_exact X.obj 0)
    (perfectTensorRight_waldhausenExact L) (IsExact.id (WK(PL(X.obj))).cof (WK(PL(X.obj))).weq)
    (negativeChartCoordinate X) (overlapCoordinateUnit X)⁻¹
    (negativeChartCoordinate_restrict X) e k h n z
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
  rw [KMap_id, MonoidHom.id_apply, htwist] at hc
  rw [projectiveLineKMap_apply, map_inv]
  change _ = z * (KMap (projectiveLineSecondSummand_exact X.obj) n a)⁻¹
  exact hc

end AlgebraicGeometry.Scheme.ProjectiveLine
