/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.IrreducibleLocalMap
public import Colib.RingTheory.AdjoinRoot.TensorSwap
public import Colib.RingTheory.AdjoinRoot.OriginGenericSquare
public import Colib.RingTheory.AdjoinRoot.ResidueField
public import StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.AffineLineResidue

/-!
# The actual polynomial local map in the inert constant case

An irreducible constant polynomial remains irreducible over the actual closed-point
quotient precisely in the inert case. Tensor swapping proves irreducibility of the
opposite polynomial. Evaluation then maps its original polynomial localization into
the actual finite local constant root algebra. The uniformizer and generic-field
squares use the original polynomial maps and rational coefficient equivalence.

The auxiliary closed point may be inseparable over the constant field. No finite
module instance is asserted for a split-branch localization.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Stacks.Chow
open scoped RatFunc
attribute [local instance] Polynomial.algebra Polynomial.irreducibleLocalMap_isPrime

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact p.Monic] [Fact (Irreducible p)] [Fact (Irreducible h)]
  [hinert : Fact (Irreducible (p.map (algebraMap k (AdjoinRoot h))))]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "R" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton h : Set k[X]))
local notation "pR" => Polynomial.map (algebraMap k R) p
local notation "S" => AdjoinRoot pR
local notation "hE" => Polynomial.map (algebraMap k E) h
local notation "U" =>
  Localization.AtPrime (Ideal.span (Singleton.singleton hE : Set E[X]))
local notation "pH" => Polynomial.map (algebraMap k H) p

local instance inertPolynomial_baseMaximal :
    (Ideal.span ({h} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial Fact.out

local instance inertPolynomial_baseDVR : IsDiscreteValuationRing R :=
  isDiscreteValuationRing_localizationAtPrime_polynomial _

omit [Fact p.Monic] in
/-- Tensor swapping detects the original opposite inert polynomial without any
separability hypothesis on either polynomial. -/
theorem irreducible_map_of_irreducible_opposite : Irreducible hE := by
  have hdom : IsDomain (AdjoinRoot hE) :=
    Function.Injective.isDomain (tensorSwapEquiv p h).toRingHom
      (tensorSwapEquiv p h).injective
  have hprime : (Ideal.span ({hE} : Set E[X])).IsPrime := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mp
    change IsDomain (AdjoinRoot hE)
    exact hdom
  exact ((Ideal.span_singleton_prime
    (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)).mp hprime).irreducible

local instance inertPolynomial_oppositeIrreducible : Fact (Irreducible hE) :=
  ⟨irreducible_map_of_irreducible_opposite p h⟩

local instance inertPolynomial_upperMaximal :
    (Ideal.span ({hE} : Set E[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial Fact.out

/-- The native base quotient comparison preserves every original polynomial. -/
theorem inertPolynomial_baseResidue_algebraMap (a : k[X]) :
    (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
      (residue R (algebraMap k[X] R a)) = mk h a := by
  rw [residue_algebraMap_eq_quotientRingEquivResidueField,
    RingEquiv.symm_apply_apply]
  rfl

omit [Fact p.Monic] [Fact (Irreducible p)] hinert in
/-- Reducing the actual local constant polynomial gives its original coefficient
extension over the closed-point quotient, through the native base dictionary. -/
theorem inertPolynomial_map_residue :
    Polynomial.map
        (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm.toRingHom
        (Polynomial.map (residue R) pR) = pH := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext a
  change (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
    (residue R (algebraMap k[X] R (C a))) = of h a
  exact inertPolynomial_baseResidue_algebraMap h (C a)

include hinert in
local instance inertPolynomial_residueIrreducible :
    Fact (Irreducible (Polynomial.map (residue R) pR)) := by
  constructor
  apply Polynomial.Monic.irreducible_of_irreducible_map
    (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm.toRingHom
    _ (((Fact.out : p.Monic).map _).map _)
  rw [inertPolynomial_map_residue p h]
  exact hinert.out

local instance inertPolynomial_sourceDomain : IsDomain S :=
  isDomain_of_irreducible_map_residue ((Fact.out : p.Monic).map _) Fact.out

local instance inertPolynomial_sourceLocal : IsLocalRing S :=
  isLocalRing_of_irreducible_map_residue ((Fact.out : p.Monic).map _) Fact.out

local instance inertPolynomial_sourceLocalHom : IsLocalHom (algebraMap R S) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact isLocalHom_of_monic ((Fact.out : p.Monic).map _)

local instance inertPolynomial_upperDVR : IsDiscreteValuationRing U :=
  isDiscreteValuationRing_localizationAtPrime_polynomial _

local instance inertPolynomial_sourceDVR : IsDiscreteValuationRing S := by
  apply AdjoinRoot.isDiscreteValuationRing ((Fact.out : p.Monic).map _) Fact.out
  rw [(Fact.out : p.Monic).natDegree_map]
  exact (Fact.out : Irreducible p).natDegree_pos

omit [Fact p.Monic] hinert in
/-- Original polynomials evaluated in the constant root algebra have their literal
base-local images. This equation fixes the coefficient map and the coordinate. -/
theorem inertPolynomial_eval₂_map (a : k[X]) :
    (a.map (algebraMap k E)).eval₂
        (map (algebraMap k R) p pR dvd_rfl)
        (of pR (algebraMap k[X] R X)) =
      of pR (algebraMap k[X] R a) := by
  have he : (Polynomial.eval₂RingHom
      (map (algebraMap k R) p pR dvd_rfl) (of pR (algebraMap k[X] R X))).comp
        (Polynomial.mapRingHom (algebraMap k E)) =
      (of pR).comp (algebraMap k[X] R) := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change map (algebraMap k R) p pR dvd_rfl (of p b) =
        of pR (algebraMap k[X] R (C b))
      rw [map_of]
      rfl
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  exact RingHom.congr_fun he a

/-- The original upper uniformizer reduces to zero in the actual root algebra. -/
theorem inertPolynomial_residue_eval₂_self :
    residue S (Polynomial.eval₂ (map (algebraMap k R) p pR dvd_rfl)
      (of pR (algebraMap k[X] R X)) hE) = 0 := by
  rw [inertPolynomial_eval₂_map]
  apply (residue_eq_zero_iff _).mpr
  exact map_nonunit (algebraMap R S) _
    (irreducible_algebraMap_self (p := h)).not_isUnit

/-- The native original polynomial localization maps to the literal finite local
constant root algebra by evaluation, with no replacement of its fraction field. -/
def inertPolynomialLocalMap : U →+* S :=
  Polynomial.localizeAtIrreducibleEval₂ hE
    (map (algebraMap k R) p pR dvd_rfl)
    (of pR (algebraMap k[X] R X)) (inertPolynomial_residue_eval₂_self p h)

/-- The local map retains evaluation on every upper polynomial. -/
theorem inertPolynomialLocalMap_algebraMap (a : E[X]) :
    inertPolynomialLocalMap p h (algebraMap E[X] U a) =
      a.eval₂ (map (algebraMap k R) p pR dvd_rfl)
        (of pR (algebraMap k[X] R X)) :=
  Polynomial.localizeAtIrreducibleEval₂_algebraMap _ _ _ _ a

local instance inertPolynomialLocalMap_isLocalHom : IsLocalHom (inertPolynomialLocalMap p h) :=
  Polynomial.isLocalHom_localizeAtIrreducibleEval₂ _ _ _ _

/-- The actual upper polynomial uniformizer is exactly the image of the base
uniformizer, not merely an associate with an unspecified unit. -/
theorem inertPolynomialLocalMap_uniformizer :
    inertPolynomialLocalMap p h (algebraMap E[X] U hE) =
      algebraMap R S (algebraMap k[X] R h) := by
  rw [inertPolynomialLocalMap_algebraMap, inertPolynomial_eval₂_map]
  rfl

/-- The actual local map has ramification index one, witnessed on the original
polynomial uniformizers. -/
theorem irreducible_inertPolynomialLocalMap_uniformizer :
    Irreducible (inertPolynomialLocalMap p h (algebraMap E[X] U hE)) := by
  rw [inertPolynomialLocalMap_uniformizer]
  apply AdjoinRoot.irreducible_algebraMap ((Fact.out : p.Monic).map _) Fact.out
  · rw [(Fact.out : p.Monic).natDegree_map]
    exact (Fact.out : Irreducible p).natDegree_pos
  · exact irreducible_algebraMap_self

/-- The actual native fraction map for the finite local constant root algebra. -/
def inertPolynomialFractionMap : S →+* AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) :=
  Stacks.AdjoinRootFraction.toMapAdjoinRoot (RatFunc k)
    (p := pR) (q := p.map (RatFunc.C : k →+* RatFunc k)) (by
      rw [Polynomial.map_map]
      congr 1
      ext a
      change RatFunc.C a = algebraMap R (RatFunc k) (algebraMap k[X] R (C a))
      rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_C])

omit [Fact p.Monic] [Fact (Irreducible p)] hinert in
/-- On all original root-field constants the actual fraction map equals the
original rational coefficient quotient map. -/
theorem inertPolynomialFractionMap_comp_constants :
    (inertPolynomialFractionMap p h).comp (map (algebraMap k R) p pR dvd_rfl) =
      map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, map_of, inertPolynomialFractionMap,
      Stacks.AdjoinRootFraction.toMapAdjoinRoot_of]
    congr 1
    change algebraMap R (RatFunc k) (algebraMap k[X] R (C a)) = RatFunc.C a
    rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_C]
  · simp only [RingHom.comp_apply, map_root, inertPolynomialFractionMap,
      Stacks.AdjoinRootFraction.toMapAdjoinRoot_root]

/-- The original upper rational field map and the actual local fraction map agree
on the original upper local ring. The coordinate and every old root-field element
are preserved. -/
theorem inertPolynomialLocalMap_generic_square :
    (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom.comp
        (algebraMap U (RatFunc E)) =
      (inertPolynomialFractionMap p h).comp (inertPolynomialLocalMap p h) := by
  apply IsLocalization.ringHom_ext (Ideal.span ({hE} : Set E[X])).primeCompl
  apply Polynomial.ringHom_ext
  · intro a
    change (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm
      (algebraMap U (RatFunc E) (algebraMap E[X] U (C a))) =
      inertPolynomialFractionMap p h
        (inertPolynomialLocalMap p h (algebraMap E[X] U (C a)))
    rw [← IsScalarTower.algebraMap_apply E[X] U (RatFunc E), RatFunc.algebraMap_C,
      rationalCoefficientAlgEquiv_symm_C, inertPolynomialLocalMap_algebraMap,
      Polynomial.eval₂_C]
    exact (RingHom.congr_fun (inertPolynomialFractionMap_comp_constants p h) a).symm
  · change (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm
      (algebraMap U (RatFunc E) (algebraMap E[X] U X)) =
      inertPolynomialFractionMap p h
        (inertPolynomialLocalMap p h (algebraMap E[X] U X))
    rw [← IsScalarTower.algebraMap_apply E[X] U (RatFunc E), RatFunc.algebraMap_X,
      rationalCoefficientAlgEquiv_symm_X, inertPolynomialLocalMap_algebraMap,
      Polynomial.eval₂_X, inertPolynomialFractionMap,
      Stacks.AdjoinRootFraction.toMapAdjoinRoot_of]
    change of (p.map RatFunc.C) (RatFunc.X : RatFunc k) =
      of (p.map RatFunc.C) (algebraMap R (RatFunc k) (algebraMap k[X] R X))
    rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_X]

set_option backward.isDefEq.respectTransparency false in
/-- The actual inert root residue field, expressed over the original closed-point
quotient. This is the native residue-root equivalence followed by coefficient transport. -/
def inertPolynomialResidueEquiv : ResidueField S ≃+* AdjoinRoot pH := by
  let e : ResidueField R ≃+* H :=
    (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
  exact (residueFieldEquivAdjoinRoot pR
      (Fact.out : Irreducible (Polynomial.map (residue R) pR))).trans
    (mapRingEquiv e (Polynomial.map (residue R) pR) pH
      (Associated.of_eq (inertPolynomial_map_residue p h)))

set_option backward.isDefEq.respectTransparency false in
omit [Fact (Irreducible p)] in
/-- The residue comparison preserves every actual base-local coefficient. -/
theorem inertPolynomialResidueEquiv_residue_of (a : R) :
    inertPolynomialResidueEquiv p h (residue S (of pR a)) =
      of pH ((quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
        (residue R a)) := by
  let e : ResidueField R ≃+* H :=
    (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
  change mapRingEquiv e (Polynomial.map (residue R) pR) pH
      (Associated.of_eq (inertPolynomial_map_residue p h))
      (residueFieldEquivAdjoinRoot pR
        (Fact.out : Irreducible (Polynomial.map (residue R) pR)) (residue S (of pR a))) =
    of pH (e (residue R a))
  rw [residueFieldEquivAdjoinRoot_residue_of, coe_mapRingEquiv, map_of]
  rfl

omit [Fact (Irreducible p)] in
/-- The original base residue algebra map is the actual coefficient map after
transport, including when the closed-point field is inseparable over k. -/
theorem inertPolynomialResidueEquiv_algebraMap (a : ResidueField R) :
    inertPolynomialResidueEquiv p h (algebraMap (ResidueField R) (ResidueField S) a) =
      algebraMap H (AdjoinRoot pH)
        ((quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm a) := by
  obtain ⟨b, rfl⟩ := residue_surjective a
  exact inertPolynomialResidueEquiv_residue_of p h b

set_option backward.isDefEq.respectTransparency false in
omit [Fact (Irreducible p)] in
/-- On all original constant-root elements, the actual residue comparison is the
existing AdjoinRoot coefficient map. -/
theorem inertPolynomialResidueEquiv_residue_map (a : E) :
    inertPolynomialResidueEquiv p h
        (residue S (map (algebraMap k R) p pR dvd_rfl a)) =
      map (algebraMap k H) p pH dvd_rfl a := by
  have he : ((inertPolynomialResidueEquiv p h).toRingHom.comp (residue S)).comp
      (map (algebraMap k R) p pR dvd_rfl) =
      map (algebraMap k H) p pH dvd_rfl := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro b
      change inertPolynomialResidueEquiv p h
          (residue S (map (algebraMap k R) p pR dvd_rfl (of p b))) =
        map (algebraMap k H) p pH dvd_rfl (of p b)
      rw [map_of, map_of, inertPolynomialResidueEquiv_residue_of]
      change of pH ((quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
        (residue R (algebraMap k[X] R (C b)))) = of pH (of h b)
      exact congrArg (of pH) (inertPolynomial_baseResidue_algebraMap h (C b))
    · change inertPolynomialResidueEquiv p h
          (residue S (map (algebraMap k R) p pR dvd_rfl (root p))) =
        map (algebraMap k H) p pH dvd_rfl (root p)
      rw [map_root, map_root]
      let e : ResidueField R ≃+* H :=
        (quotientRingEquivResidueField (Ideal.span ({h} : Set k[X]))).symm
      change mapRingEquiv e (Polynomial.map (residue R) pR) pH
          (Associated.of_eq (inertPolynomial_map_residue p h))
          (residueFieldEquivAdjoinRoot pR
            (Fact.out : Irreducible (Polynomial.map (residue R) pR))
            (residue S (root pR))) = root pH
      rw [residueFieldEquivAdjoinRoot_residue_root, coe_mapRingEquiv, map_root]
  exact RingHom.congr_fun he a

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial evaluation in the finite local root algebra reduces to the actual
whole tensor swap. Both quotient roots and all original coefficients are retained. -/
theorem inertPolynomialResidueEquiv_eval₂ (a : E[X]) :
    inertPolynomialResidueEquiv p h
        (residue S (a.eval₂ (map (algebraMap k R) p pR dvd_rfl)
          (of pR (algebraMap k[X] R X)))) =
      tensorSwapEquiv p h (mk hE a) := by
  have he : ((inertPolynomialResidueEquiv p h).toRingHom.comp (residue S)).comp
      (Polynomial.eval₂RingHom (map (algebraMap k R) p pR dvd_rfl)
        (of pR (algebraMap k[X] R X))) =
      (tensorSwapEquiv p h).toRingHom.comp (mk hE) := by
    apply Polynomial.ringHom_ext
    · intro b
      change inertPolynomialResidueEquiv p h
          (residue S ((C b).eval₂ (map (algebraMap k R) p pR dvd_rfl)
            (of pR (algebraMap k[X] R X)))) = tensorSwapEquiv p h (mk hE (C b))
      rw [Polynomial.eval₂_C, mk_C, inertPolynomialResidueEquiv_residue_map]
      exact (tensorSwapEquiv_algebraMap p h b).symm
    · change inertPolynomialResidueEquiv p h
          (residue S ((X : E[X]).eval₂ (map (algebraMap k R) p pR dvd_rfl)
            (of pR (algebraMap k[X] R X)))) = tensorSwapEquiv p h (mk hE X)
      rw [Polynomial.eval₂_X, mk_X, inertPolynomialResidueEquiv_residue_of,
        inertPolynomial_baseResidue_algebraMap]
      have hr := tensorSwapEquiv_map p h (root h)
      rw [map_root] at hr
      exact hr.symm
  exact RingHom.congr_fun he a

set_option backward.isDefEq.respectTransparency false in
/-- The actual induced residue-field map is exactly tensor swapping, after the
native quotient dictionaries. No residue-compatibility square is assumed. -/
theorem inertPolynomialResidueEquiv_comp_residueField_map :
    (inertPolynomialResidueEquiv p h).toRingHom.comp
        (ResidueField.map (inertPolynomialLocalMap p h)) =
      (tensorSwapEquiv p h).toRingHom.comp
        (quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))).symm.toRingHom := by
  let e : (E[X] ⧸ Ideal.span ({hE} : Set E[X])) ≃+* ResidueField U :=
    quotientRingEquivResidueField (Ideal.span ({hE} : Set E[X]))
  let τ : (E[X] ⧸ Ideal.span ({hE} : Set E[X])) →+* AdjoinRoot pH :=
    (tensorSwapEquiv p h).toRingHom
  change (inertPolynomialResidueEquiv p h).toRingHom.comp
    (ResidueField.map (inertPolynomialLocalMap p h)) = τ.comp e.symm.toRingHom
  apply RingHom.ext
  intro z
  obtain ⟨b, rfl⟩ := e.surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change inertPolynomialResidueEquiv p h
      (ResidueField.map (inertPolynomialLocalMap p h)
        (e (Ideal.Quotient.mk (Ideal.span ({hE} : Set E[X])) a))) =
    τ (e.symm (e (Ideal.Quotient.mk (Ideal.span ({hE} : Set E[X])) a)))
  rw [RingEquiv.symm_apply_apply]
  have he : e (Ideal.Quotient.mk (Ideal.span ({hE} : Set E[X])) a) =
      residue U (algebraMap E[X] U a) :=
    (residue_algebraMap_eq_quotientRingEquivResidueField
      (Ideal.span ({hE} : Set E[X])) a).symm
  rw [he, ResidueField.map_residue, inertPolynomialLocalMap_algebraMap]
  exact inertPolynomialResidueEquiv_eval₂ p h a

end AdjoinRoot
