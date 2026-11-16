/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectFlatUnitComposition
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartBaseProjection

/-! # The canonical coefficient on the actual Laurent overlap -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- The relative Laurent projection on the original overlap, through the two actual opens. -/
def overlapBaseProjection (X : QuasiCompactSchemes.{u}) :
    (chartOverlap X.obj).toScheme ⟶ X.obj :=
  (chartOverlap X.obj).ι ≫ (negativeChart X.obj).ι ≫ (projectiveSpaceOver 1 X.obj ↘ X.obj)

instance (X : QuasiCompactSchemes.{u}) : Flat (overlapBaseProjection X) := by
  unfold overlapBaseProjection
  infer_instance

/-- The actual overlap projection is the relative Laurent projection. -/
theorem standardOverlapLaurentIso_projection (X : QuasiCompactSchemes.{u}) :
    (standardOverlapLaurentIso X).hom ≫ (Relative.laurentProjection.app X).hom =
      overlapBaseProjection X := by
  have h := congrArg (fun z => z.hom) (Relative.minus_projection X)
  change (Relative.minus.app X).hom ≫ (Relative.polynomialProjection.app X).hom =
    (Relative.laurentProjection.app X).hom at h
  let e := (standardOverlapLaurentIso X).hom
  let m := (Relative.minus.app X).hom
  let p := (Relative.polynomialProjection.app X).hom
  let j := overlapToNegative X.obj
  let A := (standardChartPolynomialIso X 1).hom
  calc
    e ≫ (Relative.laurentProjection.app X).hom = e ≫ m ≫ p :=
      congrArg (e ≫ ·) h.symm
    _ = (e ≫ m) ≫ p := (Category.assoc e m p).symm
    _ = (j ≫ A) ≫ p := congrArg (· ≫ p) (overlapToNegative_polynomial X).symm
    _ = j ≫ (A ≫ p) := Category.assoc j A p
    _ = overlapBaseProjection X :=
      congrArg (j ≫ ·) (standardChartPolynomialIso_projection X 1)

/-- The same Laurent coordinate on the relative Laurent product. -/
def relativeLaurentCoordinateUnit (X : QuasiCompactSchemes.{u}) :
    (Γ((Relative.laurentFunctor.obj X).obj, ⊤))ˣ :=
  Units.map (pullback.snd (specULiftZIsTerminal.from X.obj)
      (laurentProjection (.of (ULift.{u} ℤ)))).appTop.hom.toMonoidHom
    (laurentCoordinate (.of (ULift.{u} ℤ)))

/-- The isomorphism of the actual overlap and Laurent product preserves the original unit. -/
theorem relativeLaurentCoordinateUnit_restrict (X : QuasiCompactSchemes.{u}) :
    Units.map (standardOverlapLaurentIso X).hom.appTop.hom.toMonoidHom
        (relativeLaurentCoordinateUnit X) = overlapCoordinateUnit X := by
  apply Units.ext
  rfl

set_option maxHeartbeats 1000000 in
-- Both actual coordinates use the same transported Laurent operation.
set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse Laurent unit on the overlap has the two original coordinates. -/
theorem connectingHom_overlapBaseProjection (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : (W X.obj).K n) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let U := (chartOverlap X.obj).toScheme
    let q := (overlapCoordinateUnit X)⁻¹
    ((projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
        (originalKSelfTrackOperation (W X.obj) (W U)
          (perfectFlatUnitHomotopy (overlapBaseProjection X) q) n a))) = (a, a⁻¹) := by
  let j := (negativeChart X.obj).ι
  let i := (chartOverlap X.obj).ι
  let π := projectiveSpaceOver 1 X.obj ↘ X.obj
  let q := (overlapCoordinateUnit X)⁻¹
  have hp := DFunLike.congr_fun
    (perfectFlatUnitHomotopy_originalKOperation_precomp i (j ≫ π) q n) a
  have hk : KMap (perfectFlatPullback_waldhausenExact (j ≫ π)) n a =
      KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
        (KMap (projectiveLineFirstSummand_exact X.obj) n a) := by
    change KMap (perfectFlatPullback_waldhausenExact (j ≫ π)) n a =
      KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
        (KMap (perfectFlatPullback_waldhausenExact π) n a)
    rw [← perfectKPullback_eq_flatPullback, ← perfectKPullback_eq_restrict,
      ← perfectKPullback_eq_flatPullback]
    exact DFunLike.congr_fun (perfectKPullback_comp j π n) a
  change originalKSelfTrackOperation _ _ _ n
      (KMap (perfectFlatPullback_waldhausenExact (j ≫ π)) n a) =
    originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy (overlapBaseProjection X) q) n a at hp
  rw [hk] at hp
  have hr := congrArg (projectiveLineKEquiv X.obj n).symm
    (connectingHom_inverseCoordinateUnit X n a)
  exact (congrArg (fun y => ((projectiveLineKEquiv X.obj n).symm
    (PerfectMayerVietoris.connectingHom j (positiveChart X.obj)
      (standardChart_cover X.obj) n y))) hp.symm).trans
    (hr.trans ((projectiveLineKEquiv X.obj n).symm_apply_apply _))

/-- The first coordinate of the actual inverse Laurent unit on the original overlap. -/
theorem firstCoordinate_connectingHom_overlapBaseProjection (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : (W X.obj).K n) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let U := (chartOverlap X.obj).toScheme
    let q := (overlapCoordinateUnit X)⁻¹
    ((projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
        (originalKSelfTrackOperation (W X.obj) (W U)
          (perfectFlatUnitHomotopy (overlapBaseProjection X) q) n a))).1 = a :=
  congrArg Prod.fst (connectingHom_overlapBaseProjection X n a)

/-- The Bass boundary on the original relative Laurent product is the first coordinate of the
genuine Mayer–Vietoris connecting map. -/
def positiveBassBoundary (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (W (Relative.laurentFunctor.obj X).obj).K (n + 1) →* (W X.obj).K n :=
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  (MonoidHom.fst _ _).comp ((projectiveLineKEquiv X.obj n).symm.toMonoidHom.comp
    ((PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n).comp
      (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1))))

/-- The canonical inverse Laurent unit operation on the original relative Laurent product. -/
def positiveBassUnitSection (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (W X.obj).K n →* (W (Relative.laurentFunctor.obj X).obj).K (n + 1) :=
  originalKSelfTrackOperation (W X.obj) (W (Relative.laurentFunctor.obj X).obj)
    (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom
      (relativeLaurentCoordinateUnit X)⁻¹) n

set_option maxHeartbeats 1000000 in
-- Both actual coordinates use the same transported Laurent operation.
set_option backward.isDefEq.respectTransparency false in
/-- Both coordinates of the actual inverse Laurent unit on the literal projection. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeGlobalUnitProjection.lean:57-74"
  "adaptation" "Both inverse coordinates on the actual Laurent projection"]
theorem positiveBassUnitSection_coordinates (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : (W X.obj).K n) :
    (projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
        (standardChart_cover X.obj) n
        (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1)
          (positiveBassUnitSection X n a))) = (a, a⁻¹) := by
  let e := (standardOverlapLaurentIso X).hom
  let p := (Relative.laurentProjection.app X).hom
  let q := (relativeLaurentCoordinateUnit X)⁻¹
  have h := DFunLike.congr_fun
    (perfectFlatUnitHomotopy_originalKOperation_postcomp e p q n) a
  have he : Units.map e.appTop.hom.toMonoidHom q = (overlapCoordinateUnit X)⁻¹ := by
    rw [map_inv, relativeLaurentCoordinateUnit_restrict]
  change KMap (perfectFlatPullback_waldhausenExact e) (n + 1)
      (positiveBassUnitSection X n a) =
    originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy (e ≫ p)
      (Units.map e.appTop.hom.toMonoidHom q)) n a at h
  have hp : e ≫ p = overlapBaseProjection X := standardOverlapLaurentIso_projection X
  have h' : KMap (perfectFlatPullback_waldhausenExact e) (n + 1)
      (positiveBassUnitSection X n a) =
    originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (overlapBaseProjection X) (overlapCoordinateUnit X)⁻¹) n a := by
    have hq := congrArg (fun r => originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy (e ≫ p) r) n a) he
    have hf : originalKSelfTrackOperation _ _
        (perfectFlatUnitHomotopy (e ≫ p) (overlapCoordinateUnit X)⁻¹) n a =
      originalKSelfTrackOperation _ _
        (perfectFlatUnitHomotopy (overlapBaseProjection X) (overlapCoordinateUnit X)⁻¹) n a := by
      exact DFunLike.congr_fun (perfectFlatUnitHomotopy_originalKOperation_congr
        hp (overlapCoordinateUnit X)⁻¹ n) a
    exact h.trans (hq.trans hf)
  change (projectiveLineKEquiv X.obj n).symm
    (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
      (standardChart_cover X.obj) n
      (KMap (perfectFlatPullback_waldhausenExact e) (n + 1)
        (positiveBassUnitSection X n a))) = (a, a⁻¹)
  exact (congrArg (fun y => ((projectiveLineKEquiv X.obj n).symm
    (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
      (standardChart_cover X.obj) n y))) h').trans
    (connectingHom_overlapBaseProjection X n a)

/-- The original inverse unit section splits the first-coordinate Bass boundary. -/
theorem positiveBassBoundary_comp_unitSection (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (positiveBassBoundary X n).comp (positiveBassUnitSection X n) = MonoidHom.id _ := by
  ext a
  exact congrArg Prod.fst (positiveBassUnitSection_coordinates X n a)

end AlgebraicGeometry.Scheme.ProjectiveLine
