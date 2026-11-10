/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRInertConstantSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalInertLocalSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeEquivarianceSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstantSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.CoefficientFactorSupport
public import Colib.RingTheory.KTheory.MilnorK.Residue.LinearPlaceTranslation
public import Colib.RingTheory.AdjoinRoot.TensorFactorMaps
public import Colib.FieldTheory.AdjoinRoot.RationalCoefficientMap

/-!
# The original unweighted finite residue square in the inert constant case

The actual constant polynomial is irreducible over the closed-point quotient.
The original upper polynomial localization maps unramifiedly to the actual finite
local constant root DVR. Japanese-DVR norm compatibility descends through its
proved generic and residue dictionaries. Simultaneous normal-prime equivariance
returns the residue norm to the original quotient fields. The complete native
factor sum is retained, using its proved singleton support in this inert case.

The closed point is arbitrary and may be inseparable over the constants. No
self-linearization multiplicity is cancelled and no norm square is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped RatFunc
attribute [local instance] Polynomial.algebra Polynomial.irreducibleLocalMap_isPrime

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  AdjoinRoot.inertPolynomial_baseMaximal
  AdjoinRoot.inertPolynomial_oppositeIrreducible
  AdjoinRoot.inertPolynomial_upperMaximal
  AdjoinRoot.inertPolynomial_residueIrreducible
  AdjoinRoot.inertPolynomial_sourceDomain
  AdjoinRoot.inertPolynomial_sourceLocal
  AdjoinRoot.inertPolynomial_sourceLocalHom
  AdjoinRoot.inertPolynomial_baseDVR
  AdjoinRoot.inertPolynomial_upperDVR
  AdjoinRoot.inertPolynomial_sourceDVR
  AdjoinRoot.inertPolynomialLocalMap_isLocalHom
  inertConstant_finite
  inertConstant_torsionFree
  inertConstant_finiteGeneric

local instance rationalInert_nativeMonic {F : Type u} [Field F] {a : ℕ}
    (p : MonicIrreducibleOfDegree F a) : Fact (poly p).Monic := ⟨monic p⟩

local instance rationalInert_nativeIrreducible {F : Type u} [Field F] {a : ℕ}
    (p : MonicIrreducibleOfDegree F a) : Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance rationalInert_rootFinite {F : Type u} [Field F] {a : ℕ}
    (p : MonicIrreducibleOfDegree F a) : Module.Finite F (AdjoinRoot (poly p)) :=
  (monic p).finite_adjoinRoot

local instance rationalInert_rationalFinite {F : Type u} [Field F] {a : ℕ}
    (p : MonicIrreducibleOfDegree F a) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance rationalInert_genericIrreducible {F : Type u} [Field F] {a : ℕ}
    (p : MonicIrreducibleOfDegree F a) :
    Fact (Irreducible ((poly p).map (RatFunc.C : F →+* RatFunc F))) :=
  ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  [hinert : Fact (Irreducible ((poly p).map (algebraMap k (AdjoinRoot (poly h)))))]

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "R" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton (poly h) : Set k[X]))
local notation "S" => AdjoinRoot (Polynomial.map (algebraMap k R) (poly p))
local notation "G" => AdjoinRoot (Polynomial.map (RatFunc.C : k →+* RatFunc k) (poly p))
local notation "hE" => Polynomial.map (algebraMap k E) (poly h)
local notation "pH" => Polynomial.map (algebraMap k H) (poly p)
local notation "U" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton hE : Set E[X]))

local instance rationalInert_residueFinite : Module.Finite H (AdjoinRoot pH) :=
  ((monic p).map _).finite_adjoinRoot

local instance rationalInert_genericFinite : Module.Finite (RatFunc k) G :=
  ((monic p).map _).finite_adjoinRoot

local instance rationalInert_constantTower : IsScalarTower k R (RatFunc k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change RatFunc.C a = algebraMap R (RatFunc k) (algebraMap k[X] R (C a))
  rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_C]

local instance rationalInert_fractionAlgebra : Algebra S G :=
  inertConstant_fractionAlgebra k R (RatFunc k) p

local instance rationalInert_fractionTower : IsScalarTower R S G :=
  inertConstant_fractionTower k R (RatFunc k) p

local instance rationalInert_isFractionRing : IsFractionRing S G :=
  inertConstant_isFractionRing k R (RatFunc k) p

include hinert in
/-- The actual upper inert point, with its original mapped polynomial and degree. -/
def inertUpperPoint : MonicIrreducibleOfDegree E e :=
  ⟨hE, (monic h).map _, AdjoinRoot.irreducible_map_of_irreducible_opposite
    (poly p) (poly h), ((monic h).natDegree_map _).trans (natDegree_eq h)⟩

/-- The actual tame-symbol map from the original upper polynomial localization
is transported by the whole tensor swap, with ramification multiplier one. -/
theorem dvrMilnorTameSymbol'_inertPolynomialLocalMap (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1)) :
    milnorKTheoryMap (AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)).toRingHom n
        (dvrMilnorTameSymbol' S G n
          (milnorKTheoryMap
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
            (n + 1) x)) =
      milnorKTheoryMap ((AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom.comp
        (quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))).symm.toRingHom) n
        (dvrMilnorTameSymbol' U (RatFunc E) n x) := by
  have hmap := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified («R» := U) («S» := S) (F := RatFunc E) («E» := G)
      (AdjoinRoot.inertPolynomialLocalMap (poly p) (poly h))
      (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
      (fun a => RingHom.congr_fun
        (AdjoinRoot.inertPolynomialLocalMap_generic_square (poly p) (poly h)) a)
      (irreducible_algebraMap_self (p := hE))
      (AdjoinRoot.irreducible_inertPolynomialLocalMap_uniformizer (poly p) (poly h))
      (1 : Sˣ) 1 (by simp) n) x
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Nat.cast_one, one_smul] at hmap
  rw [hmap]
  let y := dvrMilnorTameSymbol' U (RatFunc E) n x
  let f : ResidueField U →+* ResidueField S :=
    ResidueField.map (AdjoinRoot.inertPolynomialLocalMap (poly p) (poly h))
  let g : ResidueField S →+* AdjoinRoot pH :=
    (AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)).toRingHom
  have hcomp : milnorKTheoryMap (g.comp f) n y =
      milnorKTheoryMap g n (milnorKTheoryMap f n y) :=
    DFunLike.congr_fun (milnorKTheoryMap_comp (n := n) f g) y
  have hcoordinates := congrArg
    (fun φ : ResidueField U →+* AdjoinRoot pH => milnorKTheoryMap φ n y)
    (AdjoinRoot.inertPolynomialResidueEquiv_comp_residueField_map (poly p) (poly h))
  exact hcomp.symm.trans hcoordinates

variable [hnormal : Normal k (AdjoinRoot (poly p))]

include hnormal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original chosen residue norm returns through the proved inert residue
field equivalences to the original quotient fields. -/
theorem milnorKNorm_inertPolynomialResidueEquiv_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (z : MilnorKTheory (ResidueField S) n) :
    milnorKTheoryMap (quotientRingEquivResidueField (Ideal.span {poly h})).symm.toRingHom n
        (milnorKNorm (ResidueField R) (ResidueField S) n z) =
      milnorKNorm H (AdjoinRoot pH) n
        (milnorKTheoryMap
          (AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)).toRingHom n z) := by
  let σ : ResidueField R ≃+* H :=
    (quotientRingEquivResidueField (Ideal.span {poly h})).symm
  let τ : ResidueField S ≃+* AdjoinRoot pH :=
    AdjoinRoot.inertPolynomialResidueEquiv (poly p) (poly h)
  let : Module.Finite H (AdjoinRoot pH) := ((monic p).map _).finite_adjoinRoot
  let : IsSplittingField H (AdjoinRoot pH) pH :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal H (AdjoinRoot pH) := Normal.of_isSplittingField pH
  have hστ : τ.toRingHom.comp (algebraMap (ResidueField R) (ResidueField S)) =
      (algebraMap H (AdjoinRoot pH)).comp σ.toRingHom := by
    apply RingHom.ext
    intro a
    exact AdjoinRoot.inertPolynomialResidueEquiv_algebraMap (poly p) (poly h) a
  have hrev : τ.symm.toRingHom.comp (algebraMap H (AdjoinRoot pH)) =
      (algebraMap (ResidueField R) (ResidueField S)).comp σ.symm.toRingHom := by
    apply RingHom.ext
    intro a
    apply τ.injective
    change τ (τ.symm (algebraMap H (AdjoinRoot pH) a)) =
      τ (algebraMap (ResidueField R) (ResidueField S) (σ.symm a))
    rw [RingEquiv.apply_symm_apply]
    have ha := RingHom.congr_fun hστ (σ.symm a)
    change τ (algebraMap (ResidueField R) (ResidueField S) (σ.symm a)) =
      algebraMap H (AdjoinRoot pH) (σ (σ.symm a)) at ha
    rw [RingEquiv.apply_symm_apply] at ha
    exact ha.symm
  let : Normal (ResidueField R) (ResidueField S) :=
    Normal.of_equiv_equiv (f := σ.symm) (g := τ.symm) hrev.symm
  let : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    isSeparable_residueField_inert_constant k R p hsep
  have hprime : Nat.Prime (finrank (ResidueField R) (ResidueField S)) := by
    rw [Algebra.finrank_eq_of_equiv_equiv σ τ hστ.symm,
      (AdjoinRoot.powerBasis (((monic p).map (algebraMap k H)).ne_zero)).finrank,
      AdjoinRoot.powerBasis_dim, (monic p).natDegree_map, natDegree_eq p]
    exact hp
  let eqH : H ≃+* (k[X] ⧸ Ideal.span {poly h}) := RingEquiv.refl _
  have hnorm := milnorKNormRing_map_ringEquiv_of_normal_prime_of_separable
    hprime σ τ hστ (z : MilnorKRing (ResidueField S))
  have hquot := congrArg (milnorKRingMap eqH.toRingHom) hnorm
  have hσ : eqH.toRingHom.comp σ.toRingHom =
      (quotientRingEquivResidueField (Ideal.span {poly h})).symm.toRingHom := by
    apply RingHom.ext
    intro a
    rfl
  have hidentity (y : MilnorKRing H) :
      milnorKRingMap eqH.toRingHom y = (y : MilnorKRing (k[X] ⧸ Ideal.span {poly h})) := by
    let yq : MilnorKRing (k[X] ⧸ Ideal.span {poly h}) := y
    change milnorKRingMap (RingHom.id (k[X] ⧸ Ideal.span {poly h})) yq = yq
    exact milnorKRingMap_id_apply yq
  rw [milnorKRingMap_comp_apply, hσ, hidentity] at hquot
  apply Subtype.ext
  simp only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
    milnorKTransport_coe, coe_milnorKNorm]
  exact hquot

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unweighted actual finite-place square, before rewriting the inert
singleton as the complete native factor sum. -/
theorem monicIrreducibleResidue_milnorKNorm_ratFunc_of_inert_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      milnorKNormRing H (AdjoinRoot pH)
        (milnorKRingMap
          ((AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom :
            (E[X] ⧸ Ideal.span {poly (inertUpperPoint p h)}) →+* AdjoinRoot pH)
          (monicIrreducibleResidue (inertUpperPoint p h) (x : MilnorKRing (RatFunc E)))) := by
  let : Module.Finite H (AdjoinRoot pH) := ((monic p).map _).finite_adjoinRoot
  let : Normal (RatFunc k) (RatFunc E) :=
    AdjoinRoot.normal_ratFunc_adjoinRoot (poly p) (monic p)
  let : Algebra.IsSeparable (RatFunc k) (RatFunc E) :=
    isSeparable_ratFunc_adjoinRoot_of_separable p hsep
  have hprime : Nat.Prime (finrank (RatFunc k) (RatFunc E)) := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq p]
    exact hp
  let φ := (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm
  have hgen : milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x =
      milnorKNorm (RatFunc k) G (n + 1)
        (milnorKTheoryMap φ.toRingHom (n + 1) x) := by
    simpa only [RingEquiv.toRingHom_refl', milnorKTransport_id_apply,
      milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
      milnorKNorm_map_ringEquiv_of_normal_prime_of_separable hprime
        (RingEquiv.refl (RatFunc k)) φ.toRingEquiv
        (by apply RingHom.ext; intro a; exact φ.commutes a) (n + 1) x
  have hdvr := dvrMilnorTameSymbol'_milnorKNorm_inert_constant_of_separable
    k R (RatFunc k) p
    (Polynomial.isJapaneseRing_localizationAtPrime_of_field k (Ideal.span {poly h}))
    hsep hp n (milnorKTheoryMap φ.toRingHom (n + 1) x)
  simp only [RatFunc.algebraMap_eq_C] at hdvr
  have hlocal := dvrMilnorTameSymbol'_inertPolynomialLocalMap p h n x
  have hgeneric := congrArg
    (fun y : MilnorKTheory (RatFunc k) (n + 1) => dvrMilnorTameSymbol' R (RatFunc k) n y)
    hgen
  have hbase := congrArg
    (fun y : MilnorKTheory (ResidueField R) n =>
      (milnorKTheoryMap
        (quotientRingEquivResidueField (Ideal.span {poly h})).symm.toRingHom n y :
          MilnorKRing (k[X] ⧸ Ideal.span {poly h})))
    (hgeneric.trans hdvr)
  have hcanonical := monicIrreducibleResidue_coe_eq_canonical h n
    (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x)
  refine (hcanonical.trans hbase).trans ?_
  rw [milnorKNorm_inertPolynomialResidueEquiv_of_separable p h hsep hp, hlocal]
  let N : MilnorKRing (AdjoinRoot pH) → MilnorKRing (k[X] ⧸ Ideal.span {poly h}) :=
    fun y =>
      let z : MilnorKRing H := milnorKNormRing H (AdjoinRoot pH) y
      z
  let yU := dvrMilnorTameSymbol' U (RatFunc E) n x
  let f : ResidueField U →+* (E[X] ⧸ Ideal.span ({hE} : Set E[X])) :=
    (quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))).symm.toRingHom
  let g : (E[X] ⧸ Ideal.span ({hE} : Set E[X])) →+* AdjoinRoot pH :=
    (AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom
  have hcomp : milnorKTheoryMap (g.comp f) n yU =
      milnorKTheoryMap g n (milnorKTheoryMap f n yU) :=
    DFunLike.congr_fun (milnorKTheoryMap_comp (n := n) f g) yU
  have hcompRing := congrArg
    (fun y : MilnorKTheory (AdjoinRoot pH) n => N (y : MilnorKRing (AdjoinRoot pH)))
    hcomp
  have hupper := monicIrreducibleResidue_coe_eq_canonical (inertUpperPoint p h) n x
  have hupperMap := congrArg (milnorKRingMap g) hupper
  have hcoe : (milnorKTheoryMap g n (milnorKTheoryMap f n yU) :
      MilnorKRing (AdjoinRoot pH)) =
        milnorKRingMap g (milnorKTheoryMap f n yU :
          MilnorKRing (E[X] ⧸ Ideal.span ({hE} : Set E[X]))) := by
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
      milnorKTransport_coe g n (milnorKTheoryMap f n yU)
  exact hcompRing.trans (congrArg N (hcoe.trans hupperMap.symm))

include hinert in
set_option backward.isDefEq.respectTransparency false in
/-- The complete original factor sum in the inert case. Singleton support is
proved from the actual irreducible mapped polynomial, and the summand retains
the native tensor-swap factor quotient equivalence and simple norm. -/
theorem monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_inert
    (hsep : (poly p).Separable) (hp : d.Prime)
    (T : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hT : ∀ q, q ∈ T ↔ poly q.2 ∣ hE)
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ T.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f // poly q.2 ∣ hE} :=
          ⟨i.1, (hT i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) := by
  classical
  let q₀ := inertUpperPoint p h
  let i₀ : T := ⟨⟨e, q₀⟩, (hT _).mpr dvd_rfl⟩
  have hall (i : T) : i = i₀ := by
    apply Subtype.ext
    apply sigma_poly_injective
    exact Polynomial.eq_of_monic_of_associated (monic i.1.2) ((monic h).map _)
      ((irreducible i.1.2).associated_of_dvd
        (AdjoinRoot.irreducible_map_of_irreducible_opposite (poly p) (poly h))
        ((hT i.1).mp i.2))
  let term (i : T) : MilnorKRing H :=
    let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f // poly q.2 ∣ hE} :=
      ⟨i.1, (hT i.1).mp i.2⟩
    let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
    simpleMilnorNorm r.1.2
      (milnorKRingMap (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
        (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E))))
  change _ = ∑ i ∈ T.attach, term i
  have hsum : (∑ i ∈ T.attach, term i) = term i₀ := by
    apply Finset.sum_eq_single i₀
    · intro i _ hne
      exact (hne (hall i)).elim
    · intro hne
      exact (hne (Finset.mem_attach T i₀)).elim
  rw [hsum]
  let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f // poly q.2 ∣ hE} :=
    ⟨⟨e, q₀⟩, dvd_rfl⟩
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  let F : AdjoinRoot pH →ₐ[H] AdjoinRoot (poly r.1.2) :=
    { toRingHom := Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)
      commutes' := fun _ => rfl }
  let eF : AdjoinRoot pH ≃ₐ[H] AdjoinRoot (poly r.1.2) :=
    AlgEquiv.ofBijective F ⟨F.injective,
      Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr r.2)⟩
  let : IsSplittingField H (AdjoinRoot pH) pH :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal H (AdjoinRoot pH) := Normal.of_isSplittingField pH
  let : Algebra.IsSeparable H (AdjoinRoot pH) :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map
  have hprime : Nat.Prime (finrank H (AdjoinRoot pH)) := by
    rw [(AdjoinRoot.powerBasis (((monic p).map (algebraMap k H)).ne_zero)).finrank,
      AdjoinRoot.powerBasis_dim, (monic p).natDegree_map, natDegree_eq p]
    exact hp
  have hmap : eF.toRingHom.comp (AdjoinRoot.tensorSwapEquiv (poly p) (poly h)).toRingHom =
      (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom := by
    apply RingHom.ext
    intro a
    have hfactor := AdjoinRoot.tensorSwapFactorQuotientEquiv_factor (poly p) (poly h) q a
    have hself : Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr q.2) a = a := by
      obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective (g := hE) a
      rfl
    rw [hself] at hfactor
    exact hfactor.symm
  change monicIrreducibleResidue h
      (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
    simpleMilnorNorm r.1.2
      (milnorKRingMap (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
        (monicIrreducibleResidue q₀ (x : MilnorKRing (RatFunc E))))
  rw [monicIrreducibleResidue_milnorKNorm_ratFunc_of_inert_of_separable p h hsep hp]
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable
    hprime r.1.2 eF]
  rw [milnorKRingMap_comp_apply, hmap]
  rfl

end Stacks.Chow
