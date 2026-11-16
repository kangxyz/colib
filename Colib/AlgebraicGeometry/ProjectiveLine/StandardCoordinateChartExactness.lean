/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisZero
public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassQuotient

/-! # The image of coefficient pullback in the two standard charts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- The diagonal map of coefficients to the two original relative polynomial charts. -/
def relativePolynomialPair (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (W X.obj).K n →* ((W(Relative.polynomialFunctor.obj X).obj).K n ×
      (W(Relative.polynomialFunctor.obj X).obj).K n) :=
  (perfectKPullback (Relative.polynomialProjection.app X).hom n).prod
    (perfectKPullback (Relative.polynomialProjection.app X).hom n)

/-- Every projective-line class has the same chart restrictions as a coefficient class. -/
theorem restrictionPair_projectiveLineKEquiv (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a b : (W X.obj).K n) :
    let j := (negativeChart X.obj).ι
    let T := positiveChart X.obj
    PerfectMayerVietoris.restrictionPair j T n (projectiveLineKEquiv X.obj n (a, b)) =
      PerfectMayerVietoris.restrictionPair j T n (projectiveLineKEquiv X.obj n (a * b, 1)) := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let E := projectiveLineKEquiv X.obj n
  let δ := PerfectMayerVietoris.connectingHom j T (standardChart_cover X.obj) n
  let x := KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom)
    (n + 1) (positiveBassUnitSection X n b⁻¹)
  let c := E.symm (δ x)
  have h₁ : c.1 = b⁻¹ := DFunLike.congr_fun
    (positiveBassBoundary_comp_unitSection X n) b⁻¹
  have h₂ : c.2 = b := by
    have h := connectingHom_coordinates_product_eq_one X n x
    change c.1 * c.2 = 1 at h
    rw [h₁, inv_mul_eq_one] at h
    exact h.symm
  have hc : c = (b⁻¹, b) := Prod.ext h₁ h₂
  have hx : PerfectMayerVietoris.restrictionPair j T n (δ x) = 1 := by
    change δ x ∈ (PerfectMayerVietoris.restrictionPair j T n).ker
    rw [← PerfectMayerVietoris.range_connectingHom_eq_ker_restrictionPair j T
      (standardChart_cover X.obj)]
    exact ⟨x, rfl⟩
  have he : E (a, b) = E (a * b, 1) * δ x := by
    calc
      E (a, b) = E ((a * b, 1) * c) := by
        rw [hc]
        exact congrArg E (Prod.ext (by simp) (by simp))
      _ = E (a * b, 1) * δ x := by
        rw [map_mul]
        exact congrArg (E (a * b, 1) * ·) (E.apply_symm_apply (δ x))
  change PerfectMayerVietoris.restrictionPair j T n (E (a, b)) =
    PerfectMayerVietoris.restrictionPair j T n (E (a * b, 1))
  rw [he, map_mul, hx, mul_one]

/-- Coefficient pullback is exactly the kernel of the original difference of polynomial
restrictions, including at degree zero. -/
theorem relativePolynomialPair_range_eq_ker (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (relativePolynomialPair X n).range = (relativeLaurentDifference X n).ker := by
  let j := (negativeChart X.obj).ι
  let T := positiveChart X.obj
  let p := standardChartPolynomialIso X 0
  let m := standardChartPolynomialIso X 1
  let e := standardOverlapLaurentIso X
  let π := projectiveSpaceOver 1 X.obj ↘ X.obj
  let : CompactSpace (standardChart X.obj 0).toScheme :=
    (Scheme.homeoOfIso p).symm.compactSpace
  let : CompactSpace (standardChart X.obj 1).toScheme :=
    (Scheme.homeoOfIso m).symm.compactSpace
  let E : ((W(Relative.polynomialFunctor.obj X).obj).K n ×
      (W(Relative.polynomialFunctor.obj X).obj).K n) → _ :=
    fun z => (perfectKPullback p.hom n z.1, perfectKPullback m.hom n z.2)
  have hE : Function.Injective E := fun _ _ h =>
    Prod.ext ((perfectKPullback_iso_bijective p n).injective (congrArg Prod.fst h))
      ((perfectKPullback_iso_bijective m n).injective (congrArg Prod.snd h))
  have hfirst (z : (W X.obj).K n) :
      E (relativePolynomialPair X n z) =
        PerfectMayerVietoris.restrictionPair j T n (projectiveLineKEquiv X.obj n (z, 1)) := by
    have hleg (i : Fin 2) :
        (perfectKPullback (standardChartPolynomialIso X i).hom n).comp
          (perfectKPullback (Relative.polynomialProjection.app X).hom n) =
            perfectKPullback ((standardChart X.obj i).ι ≫ π) n := by
      rw [← perfectKPullback_comp, standardChartPolynomialIso_projection]
    have hval :
        projectiveLineKEquiv X.obj n (z, 1) = perfectKPullback π n z := by
      change projectiveLineKMap X.obj n (z, 1) = _
      rw [projectiveLineKMap_apply, map_one, mul_one, perfectKPullback_eq_flatPullback]
      rfl
    rw [hval]
    apply Prod.ext
    · have hp := hleg 0
      change _ = perfectKPullback (T.ι ≫ π) n at hp
      change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact T.ι) n
        (perfectKPullback π n z)
      rw [← perfectKPullback_eq_restrict]
      exact DFunLike.congr_fun (hp.trans (perfectKPullback_comp T.ι π n)) z
    · have hm := hleg 1
      change _ = perfectKPullback (j ≫ π) n at hm
      change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
        (perfectKPullback π n z)
      rw [← perfectKPullback_eq_restrict]
      exact DFunLike.congr_fun (hm.trans (perfectKPullback_comp j π n)) z
  have hδ : (PerfectMayerVietoris.restrictionPair j T n).range =
      (PerfectMayerVietoris.overlapDifference j T n).ker :=
    (MonoidHom.mulExact_iff.mp
      (PerfectMayerVietoris.fiveTerm_exact j T (standardChart_cover X.obj) n).2.2).symm
  have hcompare (z : ((W(Relative.polynomialFunctor.obj X).obj).K n ×
      (W(Relative.polynomialFunctor.obj X).obj).K n)) :
      z ∈ (relativeLaurentDifference X n).ker ↔
        E z ∈ (PerfectMayerVietoris.overlapDifference j T n).ker := by
    change relativeLaurentDifference X n z = 1 ↔
      PerfectMayerVietoris.overlapDifference j T n (E z) = 1
    have h := relativeLaurentDifference_comparison X n z
    change KMap (perfectFlatPullback_waldhausenExact e.hom) n
      (relativeLaurentDifference X n z) =
        PerfectMayerVietoris.overlapDifference j T n (E z) at h
    rw [← h, ← perfectKPullback_eq_flatPullback]
    constructor
    · intro hz
      rw [hz, map_one]
      rfl
    · intro hz
      apply (perfectKPullback_iso_bijective e n).injective
      rwa [map_one]
  ext z
  rw [hcompare z, ← hδ]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨projectiveLineKEquiv X.obj n (x, 1), (hfirst x).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := (projectiveLineKEquiv X.obj n).surjective y
    exact ⟨a * b, hE ((hfirst (a * b)).trans
      ((restrictionPair_projectiveLineKEquiv X n a b).symm.trans hy))⟩

end AlgebraicGeometry.Scheme.ProjectiveLine
