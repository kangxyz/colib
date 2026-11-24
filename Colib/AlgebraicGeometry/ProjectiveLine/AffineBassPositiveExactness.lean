/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Algebra.Group.ExactTransport
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisZero
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateBoundaryKernel
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentBaseChange

/-! # Mayer–Vietoris for the two polynomial charts of the projective line

The two standard charts of `ℙ¹_R` give a Mayer–Vietoris sequence on
`Spec R[t]` and `Spec R[t,t⁻¹]`. Order the positive chart first. The overlap
map is the positive restriction minus the negative restriction, and the
connecting map keeps its projective-line target.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

open PerfectMayerVietoris (perfectK)

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable (R : CommRingCat.{u})

local notation "P" => projectiveSpaceOver 1 (Spec R)
local notation "A" => Spec (CommRingCat.of (Polynomial R))
local notation "L" => Spec (CommRingCat.of (LaurentPolynomial R))
local notation "j" => Scheme.Opens.ι (negativeChart (Spec R))
local notation "T" => positiveChart (Spec R)
local notation "U" => Scheme.Opens.toScheme (chartOverlap (Spec R))

private def affineBase (R : CommRingCat.{u}) : QuasiCompactSchemes.{u} :=
  ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩

private def positiveIso : (T).toScheme ≅ A :=
  standardChartPolynomialIso (affineBase R) 0 ≪≫ (Relative.polynomialSpecIso R).symm

private def negativeIso : (negativeChart (Spec R)).toScheme ≅ A :=
  standardChartPolynomialIso (affineBase R) 1 ≪≫ (Relative.polynomialSpecIso R).symm

private def affineOverlapIso : U ≅ L :=
  standardOverlapLaurentIso (affineBase R) ≪≫ (Relative.laurentSpecIso R).symm

/-- Restriction from the projective line to the positive and negative polynomial charts. -/
def affineBassRestrictionPair (n : ℕ) : perfectK P n →* perfectK A n × perfectK A n :=
  (perfectKPullback ((positiveIso R).inv ≫ (T).ι) n).prod
    (perfectKPullback ((negativeIso R).inv ≫ j) n)

/-- Positive restriction times inverse negative restriction on the literal Laurent spectrum. -/
def affineBassLaurentDifference (n : ℕ) :
    perfectK A n × perfectK A n →* perfectK L n :=
  GroupMayerVietoris.difference (perfectKPullback (laurentToPolynomial R) n)
    (perfectKPullback (laurentMinus R) n)

/-- The two-chart connecting homomorphism after pullback along the Laurent overlap isomorphism. -/
def affineBassLaurentConnecting (n : ℕ) : perfectK L (n + 1) →* perfectK P n :=
  (PerfectMayerVietoris.connectingHom j T (standardChart_cover (Spec R)) n).comp
    (perfectKPullback (affineOverlapIso R).hom (n + 1))

/-- The two affine coordinate isomorphisms identify the pair of local K-groups. -/
def affineBassPairEquiv (n : ℕ) :
    perfectK A n × perfectK A n ≃*
      perfectK (T).toScheme n × perfectK (negativeChart (Spec R)).toScheme n :=
  MulEquiv.prodCongr
    (MulEquiv.ofBijective _ (perfectKPullback_iso_bijective (positiveIso R) n))
    (MulEquiv.ofBijective _ (perfectKPullback_iso_bijective (negativeIso R) n))

/-- The affine Laurent isomorphism identifies the K-group of the geometric overlap. -/
def affineBassOverlapEquiv (n : ℕ) : perfectK L n ≃* perfectK U n :=
  MulEquiv.ofBijective _ (perfectKPullback_iso_bijective (affineOverlapIso R) n)

/-- The chart isomorphisms identify affine and native two-open restrictions. -/
theorem affineBassRestrictionPair_square (n : ℕ) (x : perfectK P n) :
    affineBassPairEquiv R n (affineBassRestrictionPair R n x) =
      PerfectMayerVietoris.restrictionPair j T n x := by
  have h (V : (P).Opens) (e : V.toScheme ≅ A) :
      (perfectKPullback e.hom n).comp (perfectKPullback (e.inv ≫ V.ι) n) =
        perfectKPullback V.ι n := by
    rw [← perfectKPullback_comp, e.hom_inv_id_assoc]
  apply Prod.ext
  · change perfectKPullback (positiveIso R).hom n
      (perfectKPullback ((positiveIso R).inv ≫ (T).ι) n x) =
      KMap (perfectComplexesRestrictOpenImmersion_isExact (T).ι) n x
    rw [← perfectKPullback_eq_restrict]
    exact DFunLike.congr_fun (h T (positiveIso R)) x
  · change perfectKPullback (negativeIso R).hom n
      (perfectKPullback ((negativeIso R).inv ≫ j) n x) =
      KMap (perfectComplexesRestrictOpenImmersion_isExact j) n x
    rw [← perfectKPullback_eq_restrict]
    exact DFunLike.congr_fun (h (negativeChart (Spec R)) (negativeIso R)) x

private theorem overlapLeg {B V C D E F : Scheme.{u}}
    (o : B ≅ E) (b : C ≅ E) (p : V ≅ F) (a : D ≅ F)
    (k : B ⟶ V) (l : C ⟶ D) (r : E ⟶ F)
    (hk : k ≫ p.hom = o.hom ≫ r) (hl : l ≫ a.hom = b.hom ≫ r) :
    (o ≪≫ b.symm).hom ≫ l = k ≫ (p ≪≫ a.symm).hom := by
  apply (cancel_mono a.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hl, b.inv_hom_id_assoc, ← hk]

/-- The two descriptions of the overlap map agree with the positive-minus-negative convention. -/
theorem affineBassLaurentDifference_square (n : ℕ) (x : perfectK A n × perfectK A n) :
    affineBassOverlapEquiv R n (affineBassLaurentDifference R n x) =
      PerfectMayerVietoris.overlapDifference j T n (affineBassPairEquiv R n x) := by
  let X := affineBase R
  let p := (j).resLE T (j ⁻¹ᵁ T) le_rfl
  let : IsOpenImmersion p := by
    dsimp only [p]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hp : (affineOverlapIso R).hom ≫ laurentToPolynomial R = p ≫ (positiveIso R).hom := by
    apply overlapLeg (standardOverlapLaurentIso X) (Relative.laurentSpecIso R)
      (standardChartPolynomialIso X 0) (Relative.polynomialSpecIso R)
      p (laurentToPolynomial R) (Relative.plus.app X).hom
    · dsimp only [p]
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact overlapToPositive_polynomial X
    · exact Relative.polynomialLaurentSpecIso_plus R
  have hm : (affineOverlapIso R).hom ≫ laurentMinus R =
      (chartOverlap (Spec R)).ι ≫ (negativeIso R).hom :=
    overlapLeg (standardOverlapLaurentIso X) (Relative.laurentSpecIso R)
      (standardChartPolynomialIso X 1) (Relative.polynomialSpecIso R)
      (chartOverlap (Spec R)).ι (laurentMinus R) (Relative.minus.app X).hom
      (overlapToNegative_polynomial X) (Relative.polynomialLaurentSpecIso_minus R)
  have hplus : (perfectKPullback (affineOverlapIso R).hom n).comp
      (perfectKPullback (laurentToPolynomial R) n) =
        (perfectKPullback p n).comp (perfectKPullback (positiveIso R).hom n) := by
    exact (perfectKPullback_comp (affineOverlapIso R).hom (laurentToPolynomial R) n).symm.trans
      ((congrArg (fun f : U ⟶ A => perfectKPullback f n) hp).trans
        (perfectKPullback_comp p (positiveIso R).hom n))
  have hminus : (perfectKPullback (affineOverlapIso R).hom n).comp
      (perfectKPullback (laurentMinus R) n) =
        (perfectKPullback (chartOverlap (Spec R)).ι n).comp
          (perfectKPullback (negativeIso R).hom n) := by
    rw [← perfectKPullback_comp, ← perfectKPullback_comp, hm]
  change perfectKPullback (affineOverlapIso R).hom n
    (perfectKPullback (laurentToPolynomial R) n x.1 *
      (perfectKPullback (laurentMinus R) n x.2)⁻¹) = _
  rw [map_mul, map_inv]
  apply congrArg₂ (fun a b => a * b⁻¹)
  · change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact p) n
      (perfectKPullback (positiveIso R).hom n x.1)
    rw [← perfectKPullback_eq_restrict]
    exact DFunLike.congr_fun hplus x.1
  · change _ = KMap (perfectComplexesRestrictOpenImmersion_isExact (chartOverlap (Spec R)).ι) n
      (perfectKPullback (negativeIso R).hom n x.2)
    rw [← perfectKPullback_eq_restrict]
    exact DFunLike.congr_fun hminus x.2

private theorem affineBassLaurentConnecting_square_aux (n : ℕ) (x : perfectK L (n + 1)) :
    affineBassLaurentConnecting R n x =
      PerfectMayerVietoris.connectingHom j T (standardChart_cover (Spec R)) n
        (affineBassOverlapEquiv R (n + 1) x) :=
  rfl

/-- The transported connecting map is the actual Mayer–Vietoris connecting homomorphism. -/
@[colib_tag "COL-1340"]
theorem affineBassLaurentConnecting_square (n : ℕ) (x : perfectK L (n + 1)) :
    affineBassLaurentConnecting R n x =
      PerfectMayerVietoris.connectingHom j T (standardChart_cover (Spec R)) n
        (affineBassOverlapEquiv R (n + 1) x) :=
  affineBassLaurentConnecting_square_aux R n x

/-- Exactness at the three interior positions of the positive projective-line sequence on
literal polynomial and Laurent spectra, with the original projective-valued boundary. -/
@[colib_tag "COL-1340", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/BassPositiveMayerVietoris.lean:38-180"
  "adaptation" "The same affine covers, signed Laurent restrictions and projective boundary"]
theorem affineBassPositiveExactSequence (n : ℕ) :
    (affineBassRestrictionPair R (n + 1)).range = (affineBassLaurentDifference R (n + 1)).ker ∧
    (affineBassLaurentDifference R (n + 1)).range = (affineBassLaurentConnecting R n).ker ∧
    (affineBassLaurentConnecting R n).range = (affineBassRestrictionPair R n).ker := by
  let d := PerfectMayerVietoris.connectingHom j T (standardChart_cover (Spec R)) n
  have h := PerfectMayerVietoris.fiveTerm_exact j T (standardChart_cover (Spec R)) n
  refine ⟨?_, ?_, ?_⟩
  · exact MonoidHom.range_eq_ker_of_equiv _ _
      (PerfectMayerVietoris.restrictionPair j T (n + 1))
      (PerfectMayerVietoris.overlapDifference j T (n + 1))
      (MulEquiv.refl _) (affineBassPairEquiv R (n + 1)) (affineBassOverlapEquiv R (n + 1))
      (affineBassRestrictionPair_square R (n + 1)) (affineBassLaurentDifference_square R (n + 1))
      (MonoidHom.mulExact_iff.mp
        (PerfectMayerVietoris.fiveTerm_exact j T (standardChart_cover (Spec R)) (n + 1)).2.2).symm
  · exact MonoidHom.range_eq_ker_of_equiv _ _
      (PerfectMayerVietoris.overlapDifference j T (n + 1)) d
      (affineBassPairEquiv R (n + 1)) (affineBassOverlapEquiv R (n + 1)) (MulEquiv.refl _)
      (affineBassLaurentDifference_square R (n + 1)) (affineBassLaurentConnecting_square R n)
      (MonoidHom.mulExact_iff.mp h.1).symm
  · exact MonoidHom.range_eq_ker_of_equiv _ _
      d (PerfectMayerVietoris.restrictionPair j T n)
      (affineBassOverlapEquiv R (n + 1)) (MulEquiv.refl _) (affineBassPairEquiv R n)
      (affineBassLaurentConnecting_square R n) (affineBassRestrictionPair_square R n)
      (MonoidHom.mulExact_iff.mp h.2.1).symm

end AlgebraicGeometry.Scheme.ProjectiveLine
