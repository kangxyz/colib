/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateUnitProjection
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartCoefficientInjection

/-! # The kernel of the actual first-coordinate Bass boundary -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

set_option backward.isDefEq.respectTransparency false in
/-- Both projective-line summands restrict to the same coefficient functor on the negative chart. -/
def projectiveLineSecondSummandNegativeRestrictIso (X : QuasiCompactSchemes.{u}) :
    projectiveLineSecondSummand X.obj ⋙
        perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι ≅
      projectiveLineFirstSummand X.obj ⋙
        perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι := by
  let L := twistOver 1 X.obj (-1)
  let : SheafOfModules.IsFiniteLocallyFree
      (R := (projectiveSpaceOver 1 X.obj).ringCatSheaf) L :=
    let : SheafOfModules.IsFiniteLocallyFreeOfRank
        (R := (projectiveSpaceOver 1 X.obj).ringCatSheaf) L 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme
        (projectiveSpaceOver 1 X.obj) L
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  let F := projectiveLineFirstSummand X.obj
  let R := perfectComplexesRestrictOpenImmersion (negativeChart X.obj).ι
  exact Functor.associator F (perfectTensorLeft L) R ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight (perfectTensorLeftRightIso L) R ≪≫
      negativeChartPerfectFrame X)

/-- Negative restriction of the genuine first projective summand is the actual chart projection. -/
theorem projectiveLineFirstSummandNegativeRestrict_KMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact (negativeChart X.obj).ι) n).comp
        (KMap (projectiveLineFirstSummand_exact X.obj) n) =
      perfectKPullback ((negativeChart X.obj).ι ≫
        (projectiveSpaceOver 1 X.obj ↘ X.obj)) n := by
  let j := (negativeChart X.obj).ι
  let π := projectiveSpaceOver 1 X.obj ↘ X.obj
  change (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
    (KMap (perfectFlatPullback_waldhausenExact π) n) = _
  rw [← perfectKPullback_eq_restrict, ← perfectKPullback_eq_flatPullback, perfectKPullback_comp]

/-- The two actual summands have the same restriction K-map on the negative chart. -/
theorem projectiveLineSecondSummandNegativeRestrict_KMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact (negativeChart X.obj).ι) n).comp
        (KMap (projectiveLineSecondSummand_exact X.obj) n) =
      perfectKPullback ((negativeChart X.obj).ι ≫
        (projectiveSpaceOver 1 X.obj ↘ X.obj)) n := by
  rw [← projectiveLineFirstSummandNegativeRestrict_KMap]
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (projectiveLineSecondSummandNegativeRestrictIso X) n

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- Under the genuine two-summand isomorphism, restriction to the negative chart sends
`(a,b)` to the pullback of `ab`. -/
theorem projectiveLineKEquiv_negativeRestrict (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a b : (W X.obj).K n) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact (negativeChart X.obj).ι) n
      (projectiveLineKEquiv X.obj n (a, b)) =
    perfectKPullback ((negativeChart X.obj).ι ≫
      (projectiveSpaceOver 1 X.obj ↘ X.obj)) n (a * b) := by
  change KMap _ n (projectiveLineKMap X.obj n (a, b)) = _
  rw [projectiveLineKMap_apply, map_mul, map_mul]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (projectiveLineFirstSummandNegativeRestrict_KMap X n) a)
    (DFunLike.congr_fun (projectiveLineSecondSummandNegativeRestrict_KMap X n) b)

/-- A global class in the image of the actual Mayer–Vietoris boundary has coordinate product
one, detected on the negative chart by its split coefficient injection. -/
theorem connectingHom_coordinates_product_eq_one (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (x : (W((chartOverlap X.obj).toScheme)).K (n + 1)) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    let y := PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n x
    let c := (projectiveLineKEquiv X.obj n).symm y
    c.1 * c.2 = 1 := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let δ := PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
  let c := (projectiveLineKEquiv X.obj n).symm (δ x)
  have h : δ x ∈ (PerfectMayerVietoris.restrictionPair j T n).ker := by
    rw [← PerfectMayerVietoris.range_connectingHom_eq_ker_restrictionPair j T
      (standardChart_cover X.obj)]
    exact ⟨x, rfl⟩
  have h' : KMap (perfectComplexesRestrictOpenImmersion_isExact j) n (δ x) = 1 :=
    congrArg Prod.snd h
  apply standardChartCoefficientPullback_injective X 1 n
  change perfectKPullback (j ≫ (projectiveSpaceOver 1 X.obj ↘ X.obj)) n (c.1 * c.2) =
    perfectKPullback (j ≫ (projectiveSpaceOver 1 X.obj ↘ X.obj)) n 1
  rw [map_one]
  exact (projectiveLineKEquiv_negativeRestrict X n c.1 c.2).symm.trans
    ((congrArg (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n)
      ((projectiveLineKEquiv X.obj n).apply_symm_apply (δ x))).trans h')

/-- The first-coordinate Bass boundary and the genuine relative connecting map have the same
kernel. -/
theorem positiveBassBoundary_ker (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (positiveBassBoundary X n).ker =
      ((PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
        (standardChart_cover X.obj) n).comp
        (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom)
          (n + 1))).ker := by
  ext x
  let z := KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1) x
  let δ := PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
    (standardChart_cover X.obj) n
  let e := projectiveLineKEquiv X.obj n
  let c := e.symm (δ z)
  change c.1 = 1 ↔ δ z = 1
  constructor
  · intro h
    have hc : c = 1 := by
      apply Prod.ext
      · exact h
      · have hp := connectingHom_coordinates_product_eq_one X n z
        change c.1 * c.2 = 1 at hp
        change c.2 = 1
        simpa only [h, one_mul] using hp
    exact (e.apply_symm_apply (δ z)).symm.trans ((congrArg e hc).trans (map_one e))
  · intro h
    change (e.symm (δ z)).1 = 1
    rw [h, map_one]
    rfl

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The signed difference of restrictions to the original relative Laurent product. -/
def relativeLaurentDifference (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (W(Relative.polynomialFunctor.obj X).obj).K n ×
      (W(Relative.polynomialFunctor.obj X).obj).K n →*
      (W(Relative.laurentFunctor.obj X).obj).K n :=
  GroupMayerVietoris.difference (perfectKPullback (Relative.plus.app X).hom n)
    (perfectKPullback (Relative.minus.app X).hom n)

/-- The actual Laurent-product and overlap differences agree under the chart isomorphisms. -/
theorem relativeLaurentDifference_comparison (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (d : ℕ)
    (x : (W(Relative.polynomialFunctor.obj X).obj).K d ×
      (W(Relative.polynomialFunctor.obj X).obj).K d) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) d
      (relativeLaurentDifference X d x) =
    PerfectMayerVietoris.overlapDifference j T d
      (perfectKPullback (standardChartPolynomialIso X 0).hom d x.1,
        perfectKPullback (standardChartPolynomialIso X 1).hom d x.2) := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let e := standardOverlapLaurentIso X
  let p := standardChartPolynomialIso X 0
  let m := standardChartPolynomialIso X 1
  rw [← perfectKPullback_eq_flatPullback]
  change perfectKPullback e.hom d
    (perfectKPullback (Relative.plus.app X).hom d x.1 *
      (perfectKPullback (Relative.minus.app X).hom d x.2)⁻¹) = _
  rw [map_mul, map_inv]
  let : IsOpenImmersion (j.resLE T (j ⁻¹ᵁ T) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  apply congrArg₂ (fun a b => a * b⁻¹)
  · change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact
      (j.resLE T (j ⁻¹ᵁ T) le_rfl)) d (perfectKPullback p.hom d x.1)
    rw [← perfectKPullback_eq_restrict]
    have hleg := overlapToPositive_polynomial X
    change (j ∣_ T) ≫ p.hom = e.hom ≫ (Relative.plus.app X).hom at hleg
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact DFunLike.congr_fun ((perfectKPullback_comp e.hom _ d).symm.trans
      ((congrArg (fun f => perfectKPullback f d) hleg.symm).trans
        (perfectKPullback_comp (j ∣_ T) p.hom d))) x.1
  · change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact
      (j ⁻¹ᵁ T).ι) d (perfectKPullback m.hom d x.2)
    rw [← perfectKPullback_eq_restrict]
    have hleg := overlapToNegative_polynomial X
    exact DFunLike.congr_fun ((perfectKPullback_comp e.hom _ d).symm.trans
      ((congrArg (fun f => perfectKPullback f d) hleg.symm).trans
        (perfectKPullback_comp (j ⁻¹ᵁ T).ι m.hom d))) x.2

/-- Pullback along a scheme isomorphism is bijective on the genuine perfect K-groups. -/
theorem perfectKPullback_iso_bijective {A B : Scheme.{u}} [CompactSpace A] [CompactSpace B]
    (e : A ≅ B) (d : ℕ) : Function.Bijective (perfectKPullback e.hom d) := by
  have hl := (perfectKPullback_comp e.inv e.hom d).symm.trans
    ((congrArg (fun f => perfectKPullback f d) e.inv_hom_id).trans (perfectKPullback_id B d))
  have hr := (perfectKPullback_comp e.hom e.inv d).symm.trans
    ((congrArg (fun f => perfectKPullback f d) e.hom_inv_id).trans (perfectKPullback_id A d))
  have hl' : Function.LeftInverse (perfectKPullback e.inv d) (perfectKPullback e.hom d) :=
    fun x => DFunLike.congr_fun hl x
  have hr' : Function.RightInverse (perfectKPullback e.inv d) (perfectKPullback e.hom d) :=
    fun x => DFunLike.congr_fun hr x
  exact ⟨hl'.injective, hr'.surjective⟩

private theorem standardChart_compact (X : QuasiCompactSchemes.{u}) (i : Fin 2) :
    CompactSpace (standardChart X.obj i).toScheme :=
  (Scheme.homeoOfIso (standardChartPolynomialIso X i)).symm.compactSpace

/-- Exactness on the original relative Laurent product, through the actual Bass boundary. -/
theorem relativeLaurentDifference_range_eq_ker (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (relativeLaurentDifference X (n + 1)).range = (positiveBassBoundary X n).ker := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let e := standardOverlapLaurentIso X
  let p := standardChartPolynomialIso X 0
  let m := standardChartPolynomialIso X 1
  let d := n + 1
  let δ := PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
  let E := KMap (perfectFlatPullback_waldhausenExact e.hom) d
  let : CompactSpace (standardChart X.obj 0).toScheme := standardChart_compact X 0
  let : CompactSpace (standardChart X.obj 1).toScheme := standardChart_compact X 1
  have hker := PerfectMayerVietoris.range_overlapDifference_eq_ker_connectingHom j T
    (standardChart_cover X.obj) n
  have hE : Function.Injective E := by
    change Function.Injective (KMap (perfectFlatPullback_waldhausenExact e.hom) d)
    rw [← perfectKPullback_eq_flatPullback]
    exact (perfectKPullback_iso_bijective e d).1
  rw [positiveBassBoundary_ker]
  ext y
  change y ∈ (relativeLaurentDifference X d).range ↔ δ (E y) = 1
  constructor
  · rintro ⟨x, rfl⟩
    rw [relativeLaurentDifference_comparison]
    change _ ∈ δ.ker
    rw [← hker]
    exact ⟨_, rfl⟩
  · intro hy
    have hmem : E y ∈ (PerfectMayerVietoris.overlapDifference j T d).range := by
      rw [hker]
      exact hy
    obtain ⟨x, hx⟩ := hmem
    have hp := (perfectKPullback_iso_bijective p d).2
    have hm := (perfectKPullback_iso_bijective m d).2
    obtain ⟨a, ha⟩ := hp x.1
    obtain ⟨b, hb⟩ := hm x.2
    refine ⟨(a, b), hE ?_⟩
    rw [relativeLaurentDifference_comparison, ha, hb]
    exact hx

end AlgebraicGeometry.Scheme.ProjectiveLine
