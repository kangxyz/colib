/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalMiddleList
public import Colib.RingTheory.Koszul.GenericEuler
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The actual remaining prime-quotient Euler factor is an ambient Tor coefficient

Let `R` be the full intermediate-image exterior stalk at the image of a remaining-incidence
point, and `B` the whole original finite algebra over that stalk. For an original prime `q`
of `B`, keep its literal contraction `p` to `R`. Native stalk-prime geometry identifies `p`
with the ideal stalk of the integral closure of the corresponding image-exterior point.
The prime need not be minimal: vertical and nonminimal contractions are retained here, and
no such closure is declared an admissible finite correspondence.

Let `C` be the actual remaining fourfold ambient stalk. Its actual closed-image map to `R`
is surjective. A regular family on the original Z self-product pulls to a regular family in
`C`, generating the actual remaining-diagonal ideal `J`. Native quotient Tor and coefficient
restriction identify `Tor_C(R/p, C/J)` with the original remaining Koszul homology. Length is
transferred only along the actual surjection `C → R`, not along the middle-stalk map. The native
Koszul resolution bounds the Tor degrees, so the final signed equality uses an unbounded finsum
without a caller-supplied cutoff. Smoothness supplies an original regular family at this point.

This identifies each prime-quotient factor in the signed generic Euler formula, with the
same prime label and coefficients. It does not reindex original generic labels, remove
vertical terms, prove admissibility, or identify a complete global bracket.

Native providers: `IdealSheafData.stalk_comap`,
`idealStalk_vanishingIdeal_closure_fromSpecStalk`, the regular Koszul quotient Tor comparison,
and `Module.length_eq_of_surjective`. No comparison or replacement action is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

private theorem map_primeComparison_idealStalk_congr {T : Scheme.{u}} (I : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk I a).map
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom =
        IdealSheafData.stalk I b := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual image-exterior inclusion commutes with the original remaining middle pair. -/
@[reassoc]
theorem correspondenceLeftImageProductInclusion_middlePair :
    correspondenceLeftImageProductInclusion f g h i z w v ≫ correspondenceMiddlePair f h i =
      correspondenceLeftImageMiddlePair f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceLeftImageProductInclusion, correspondenceMiddlePair,
      correspondenceLeftImageMiddlePair, correspondenceIntermediateImageTarget, Category.assoc]

variable (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "e" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "c" =>
  correspondenceLeftImageProductInclusion f g h i z w v e
local notation3 (prettyPrint := false) "m" =>
  correspondenceLeftImageMiddlePair f g h i z w v e
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk m
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x

/-- Native smooth-diagonal regularity chooses the family at the actual remaining middle point. -/
theorem exists_correspondenceRemainingOriginalMiddleList [Smooth h] [IsSeparated h] :
    ∃ (r : ℕ) (s : Fin r → A), IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s) := by
  let y := (pullback.fst (correspondenceIntermediateImageTarget f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫
      correspondenceIntermediateImageTarget f g h z w) x
  have hp : pullback.diagonal h y = m := by
    simpa only [y, Scheme.Hom.comp_apply] using
      congrArg (fun k => k x) (correspondenceLeftImageMiddlePair_isPullback f g h i z w v).w.symm
  have hex : ∃ l : List ((pullback h h).presheaf.stalk (pullback.diagonal h y)),
      IsRegular ((pullback h h).presheaf.stalk (pullback.diagonal h y)) l ∧
        IdealSheafData.stalk (pullback.diagonal h).ker (pullback.diagonal h y) =
          Ideal.ofList l := by
    obtain ⟨l, hl, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        (pullback.diagonal h)
        (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst h h) (pullback.diagonal h) (pullback.diagonal_fst h)) y
    exact ⟨l, hl, (ker_stalkMap_eq_idealStalk_ker (pullback.diagonal h) y).symm.trans hk.symm⟩
  rw [hp] at hex
  obtain ⟨l, hl, hk⟩ := hex
  refine ⟨l.length, l.get, ?_, ?_⟩
  · simpa only [List.ofFn_get] using hl
  · rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk

/-- The actual remaining fourfold ambient local ring, before the remaining diagonal quotient. -/
abbrev correspondenceRemainingAmbientStalk :=
  (correspondenceIntersectionAmbient f h i).presheaf.stalk c

/-- The actual closed image-exterior stalk map; its target is not the incidence quotient. -/
abbrev correspondenceRemainingImageAmbientStalkMap :
    correspondenceRemainingAmbientStalk f g h i z w v x →+* R :=
  ((correspondenceLeftImageProductInclusion f g h i z w v).stalkMap e).hom

/-- The actual ambient-to-image-exterior scalar map is surjective. -/
theorem correspondenceRemainingImageAmbientStalkMap_surjective :
    Function.Surjective (correspondenceRemainingImageAmbientStalkMap f g h i z w v x) :=
  SurjectiveOnStalks.stalkMap_surjective
    (correspondenceLeftImageProductInclusion f g h i z w v) e

/-- The two actual presentations of the original remaining middle point coincide. -/
theorem correspondenceRemainingMiddle_point_eq : m = correspondenceMiddlePair f h i c := by
  simpa only [Scheme.Hom.comp_apply] using
    (congrArg (fun k => k e)
      (correspondenceLeftImageProductInclusion_middlePair f g h i z w v)).symm

/-- The original remaining middle stalk maps to the actual ambient, with its point transport. -/
def correspondenceRemainingAmbientMiddleStalkMap :
    A →+* correspondenceRemainingAmbientStalk f g h i z w v x :=
  (((pullback h h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceRemainingMiddle_point_eq f g h i z w v x))).hom ≫
      (correspondenceMiddlePair f h i).stalkMap c).hom

/-- The actual ambient route is exactly the original remaining image-exterior scalar map. -/
theorem correspondenceRemainingImageAmbientStalkMap_comp_middle :
    (correspondenceRemainingImageAmbientStalkMap f g h i z w v x).comp
      (correspondenceRemainingAmbientMiddleStalkMap f g h i z w v x) = α := by
  have he := Scheme.Hom.stalkMap_congr_hom
    (correspondenceLeftImageMiddlePair f g h i z w v)
    (correspondenceLeftImageProductInclusion f g h i z w v ≫ correspondenceMiddlePair f h i)
    (correspondenceLeftImageProductInclusion_middlePair f g h i z w v).symm e
  change ((((pullback h h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceRemainingMiddle_point_eq f g h i z w v x))).hom ≫
      (correspondenceMiddlePair f h i).stalkMap c) ≫
        (correspondenceLeftImageProductInclusion f g h i z w v).stalkMap e).hom = _
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact congrArg (fun a => a.hom) he.symm

local notation3 (prettyPrint := false) "C" =>
  correspondenceRemainingAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "ρ" =>
  correspondenceRemainingImageAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "β" =>
  correspondenceRemainingAmbientMiddleStalkMap f g h i z w v x

/-- The defining ideal of the actual remaining diagonal in the actual fourfold ambient stalk. -/
abbrev correspondenceRemainingDiagonalStalkIdeal : Ideal C :=
  IdealSheafData.stalk (correspondenceTripleInclusion f h i).ker c

/-- The original remaining family is regular in the ambient and generates its actual diagonal. -/
theorem correspondenceRemainingOriginalList_ambient_regular [Flat f] [Flat i] [IsSeparated h]
    {r : ℕ} (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) :
    IsRegular C (List.ofFn (fun j => β (s j))) ∧
      correspondenceRemainingDiagonalStalkIdeal f g h i z w v x =
        Ideal.span (Set.range (fun j => β (s j))) := by
  constructor
  · let : Algebra A C := (β).toAlgebra
    have : Module.Flat A C := by
      apply RingHom.Flat.comp
      · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
      · exact Flat.stalkMap (correspondenceMiddlePair f h i) c
    have : IsLocalHom (algebraMap A C) := by
      change IsLocalHom (β)
      unfold correspondenceRemainingAmbientMiddleStalkMap
      have := CommRingCat.isLocalHom_of_iso ((pullback h h).presheaf.stalkCongr
        (Inseparable.of_eq (correspondenceRemainingMiddle_point_eq f g h i z w v x)))
      exact CommRingCat.isLocalHom_comp _ _
    have : Module.FaithfullyFlat A C := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have ht : IsRegular C ((List.ofFn s).map (algebraMap A C)) := hr.of_faithfullyFlat
    change IsRegular C ((List.ofFn s).map β) at ht
    simpa only [List.map_ofFn, Function.comp_def] using ht
  · have hk : (correspondenceTripleInclusion f h i).ker =
        (pullback.diagonal h).ker.comap (correspondenceMiddlePair f h i) := by
      let sq := (correspondenceTriple_isPullback f h i).flip
      rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have ht := map_primeComparison_idealStalk_congr (pullback.diagonal h).ker
      (correspondenceRemainingMiddle_point_eq f g h i z w v x)
    change IdealSheafData.stalk (correspondenceTripleInclusion f h i).ker c = _
    rw [hk, IdealSheafData.stalk_comap, ← ht, Ideal.map_map]
    change (IdealSheafData.stalk (pullback.diagonal h).ker m).map β = _
    rw [hs, Ideal.map_span, ← Set.range_comp]
    rfl

/-- The literal contraction of an original finite-algebra prime; nonminimal primes are allowed. -/
def correspondenceRemainingImagePrime (q : PrimeSpectrum B) : PrimeSpectrum R :=
  letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
  PrimeSpectrum.comap (algebraMap R B) q

/-- The prime is literally contracted along the native whole-finite-algebra scalar map. -/
theorem correspondenceRemainingImagePrime_asIdeal (q : PrimeSpectrum B) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal =
      q.asIdeal.comap (algebraMap R B) := rfl

/-- The actual integral prime closure in the full image exterior, not an admissibility claim. -/
abbrev correspondenceRemainingImagePrimeClosure (q : PrimeSpectrum B) :=
  integralComponentAt
    ((correspondenceLeftIntermediateImageProduct f g h i z w v).fromSpecStalk e
      (correspondenceRemainingImagePrime f g h i z w v x q))

/-- The actual prime-closure ideal stalk is the original literal contracted prime. -/
theorem correspondenceRemainingImagePrimeClosure_stalk (q : PrimeSpectrum B) :
    IdealSheafData.stalk (correspondenceRemainingImagePrimeClosure f g h i z w v x q) e =
      (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal :=
  idealStalk_vanishingIdeal_closure_fromSpecStalk e _

/-- The original prime-quotient coefficient with its actual remaining ambient action. -/
abbrev correspondenceRemainingImagePrimeModule (q : PrimeSpectrum B) : ModuleCat.{u} C :=
  (ModuleCat.restrictScalars ρ).obj
    (ModuleCat.of R (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal))

/-- Native remaining Tor against the actual diagonal, retaining the original source prime label. -/
abbrev correspondenceRemainingImagePrimeTor (q : PrimeSpectrum B) (n : ℕ) : ModuleCat.{u} C :=
  ((Tor (ModuleCat C) n).obj (correspondenceRemainingImagePrimeModule f g h i z w v x q)).obj
    (ModuleCat.of C (C ⧸ correspondenceRemainingDiagonalStalkIdeal f g h i z w v x))

/-- Degreewise native Tor is the original remaining Koszul homology, with all actual maps. -/
def correspondenceRemainingImagePrimeTorIsoKoszul [Flat f] [Flat i] [IsSeparated h]
    (q : PrimeSpectrum B) {r : ℕ} (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) (n : ℕ) :
    correspondenceRemainingImagePrimeTor f g h i z w v x q n ≅
      (ModuleCat.restrictScalars ρ).obj
        ((Koszul.seqComplexTensor (fun j => α (s j))
          (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal)).homology n) := by
  letI : Algebra C R := (ρ).toAlgebra
  let a : Fin r → C := fun j => β (s j)
  let p := (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal
  let M := correspondenceRemainingImagePrimeModule f g h i z w v x q
  let J := correspondenceRemainingDiagonalStalkIdeal f g h i z w v x
  let Q := ModuleCat.of C (C ⧸ J)
  obtain ⟨ha, hJ⟩ := correspondenceRemainingOriginalList_ambient_regular f g h i z w v x s hr hs
  have hlist : (fun j => ρ (a j)) = (fun j => α (s j)) := by
    funext j
    exact congrArg (fun ψ : A →+* R => ψ (s j))
      (correspondenceRemainingImageAmbientStalkMap_comp_middle f g h i z w v x)
  exact (((Tor_iso_Tor' C n) ≪≫ (torFlip_iso_Tor' C n).symm).app M).app Q ≪≫
    Koszul.torIsoHomologySeqComplexTensorOfIsRegular a ha J hJ M n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of R (R ⧸ p)) n ≪≫
    (ModuleCat.restrictScalars ρ).mapIso
      (eqToIso (congrArg (fun bs : Fin r → R =>
        (Koszul.seqComplexTensor bs (R ⧸ p)).homology n) hlist))

/-- Tor length equals the prime-quotient Koszul length along the actual surjective ambient map. -/
theorem length_correspondenceRemainingImagePrimeTor [Flat f] [Flat i] [IsSeparated h]
    (q : PrimeSpectrum B) {r : ℕ} (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) (n : ℕ) :
    Module.length C (correspondenceRemainingImagePrimeTor f g h i z w v x q n) =
      Module.length R ((Koszul.seqComplexTensor (fun j => α (s j))
        (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal)).homology n) := by
  letI : Algebra C R := (ρ).toAlgebra
  let H := (Koszul.seqComplexTensor (fun j => α (s j))
    (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal)).homology n
  letI : Module C H := Module.compHom H ρ
  letI : IsScalarTower C R H := IsScalarTower.of_compHom C R H
  let eTor := correspondenceRemainingImagePrimeTorIsoKoszul f g h i z w v x q s hr hs n
  have hlen := eTor.toLinearEquiv.length_eq
  exact hlen.trans (Module.length_eq_of_surjective
    (correspondenceRemainingImageAmbientStalkMap_surjective f g h i z w v x))

/-- The prime-quotient Euler factor is a signed sum of actual remaining ambient Tor lengths. -/
theorem seqEuler_correspondenceRemainingImagePrime_eq_sum_tor
    [Flat f] [Flat i] [IsSeparated h] (q : PrimeSpectrum B) {r : ℕ}
    (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j))
        (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal) =
      ∑ n : Fin (r + 1), (-1 : ℤ) ^ (n : ℕ) *
        ((Module.length C
          (correspondenceRemainingImagePrimeTor f g h i z w v x q n)).toNat : ℤ) := by
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [length_correspondenceRemainingImagePrimeTor f g h i z w v x q s hr hs]

/-- The actual remaining Tor has the native Koszul resolution bound, not a chosen cutoff. -/
theorem isZero_correspondenceRemainingImagePrimeTor_of_lt
    [Flat f] [Flat i] [IsSeparated h] (q : PrimeSpectrum B) {r : ℕ}
    (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s))
    {n : ℕ} (hn : r < n) :
    IsZero (correspondenceRemainingImagePrimeTor f g h i z w v x q n) := by
  let a : Fin r → C := fun j => β (s j)
  let M := correspondenceRemainingImagePrimeModule f g h i z w v x q
  let J := correspondenceRemainingDiagonalStalkIdeal f g h i z w v x
  let Q := ModuleCat.of C (C ⧸ J)
  obtain ⟨ha, hJ⟩ := correspondenceRemainingOriginalList_ambient_regular f g h i z w v x s hr hs
  let eflip := (((Tor_iso_Tor' C n) ≪≫ (torFlip_iso_Tor' C n).symm).app M).app Q
  refine IsZero.of_iso ?_ (eflip ≪≫ ((Tor_iso_Tor' C n).app Q).app M)
  change IsZero (((Tor' (ModuleCat C) n).obj (ModuleCat.of C (C ⧸ J))).obj M)
  rw [hJ]
  exact Koszul.isZero_tor_of_lt a
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := C)).2.2 ha) M hn

/-- The prime-quotient factor equals the full signed remaining Tor coefficient in all degrees. -/
theorem seqEuler_correspondenceRemainingImagePrime_eq_finsum_tor
    [Flat f] [Flat i] [IsSeparated h] (q : PrimeSpectrum B) {r : ℕ}
    (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j))
        (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length C
          (correspondenceRemainingImagePrimeTor f g h i z w v x q n)).toNat : ℤ) := by
  rw [seqEuler_correspondenceRemainingImagePrime_eq_sum_tor f g h i z w v x q s hr hs,
    Fin.sum_univ_eq_sum_range]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  by_contra hnr
  have hz := isZero_correspondenceRemainingImagePrimeTor_of_lt
    f g h i z w v x q s hr hs (lt_of_not_ge hnr)
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  apply hn
  simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]

end Stacks.Chow
