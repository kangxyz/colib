/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.PurelyInseparable
public import Colib.RingTheory.AdjoinRoot.TensorFactorMaps
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
import Colib.RingTheory.KTheory.MilnorK.Dedekind.PurePrimeResiduePushforward
import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange
import Colib.RingTheory.KTheory.MilnorK.Residue.LinearPlaceTranslation
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Finite rational-place residues for purely inseparable prime constants

The finite Dedekind model is the original polynomial ring over the upper
constants. The native polynomial-place dictionary and the actual tensor swap
identify its branch norm with the simple norm of the matching factor.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing IsDedekindDomain Module AdicCompletion
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Classical.decEq Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

local instance rationalPure_nativeIrreducible {K : Type u} [Field K] {a : ℕ}
    (p : MonicIrreducibleOfDegree K a) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalPure_rootFinite {K : Type u} [Field K] {a : ℕ}
    (p : MonicIrreducibleOfDegree K a) : Module.Finite K (AdjoinRoot (poly p)) :=
  (monic p).finite_adjoinRoot

local instance rationalPure_rationalFinite {K : Type u} [Field K] {a : ℕ}
    (p : MonicIrreducibleOfDegree K a) :
    Module.Finite (RatFunc K) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ} (p : MonicIrreducibleOfDegree k d)

local notation "E" => AdjoinRoot (poly p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-place residue of a purely inseparable prime-degree
constant norm is the simple norm on the original tensor-matched branch. -/
theorem monicIrreducibleResidue_milnorKNorm_ratFunc_eq_tensorSwap_of_isPurelyInseparable
    [IsPurelyInseparable k E] (hp : d.Prime) (h : MonicIrreducibleOfDegree k e)
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
      simpleMilnorNorm r.1.2
        (@milnorKRingMap
          (E[X] ⧸ Ideal.span {poly q.1.2}) ((AdjoinRoot (poly h))[X] ⧸ Ideal.span {poly r.1.2})
          (Ideal.Quotient.field _) (Ideal.Quotient.field _)
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
          (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) := by
  classical
  let P : Ideal k[X] := Ideal.span {poly h}
  let Q : Ideal E[X] := Ideal.span {poly q.1.2}
  let R := Localization.AtPrime P
  let U := Localization.AtPrime Q
  let H := AdjoinRoot (poly h)
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  let G := AdjoinRoot (poly r.1.2)
  let : P.IsMaximal := isMaximal_span_singleton_of_irreducible_polynomial (irreducible h)
  let : Q.IsMaximal := isMaximal_span_singleton_of_irreducible_polynomial (irreducible q.1.2)
  let : Algebra R (RatFunc k) := algebraLocalizationAtPrimeRatFunc P
  let : Algebra U (RatFunc E) := algebraLocalizationAtPrimeRatFunc Q
  let : IsFractionRing R (RatFunc k) := isFractionRingLocalizationAtPrimeRatFunc P
  let : IsFractionRing U (RatFunc E) := isFractionRingLocalizationAtPrimeRatFunc Q
  let : IsScalarTower k[X] R (RatFunc k) := isScalarTowerLocalizationAtPrimeRatFunc P
  let : IsScalarTower E[X] U (RatFunc E) := isScalarTowerLocalizationAtPrimeRatFunc Q
  let bP : HeightOneSpectrum k[X] :=
    ⟨P, inferInstance, ne_bot_of_isMaximal_polynomial P⟩
  let : Module.Finite k[X] E[X] :=
    Module.Finite.equiv (Algebra.IsPushout.equiv k k[X] E E[X]).toLinearEquiv
  let : Module.IsTorsionFree k[X] E[X] :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (Polynomial.map_injective _ (algebraMap k E).injective)
  have hQP : Q.under k[X] = P :=
    Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map
      (algebraMap k E) (irreducible h) (irreducible q.1.2).not_isUnit q.2
  let bQ : IdealBranch (bP.asIdeal.map (algebraMap k[X] E[X])) :=
    Localization.primesOverEquivIdealBranch P bP.ne_bot ⟨Q, inferInstance, ⟨hQP.symm⟩⟩
  let : Algebra R U := Localization.basePrimeLocalAlgebra P Q hQP
  let : IsLocalHom (algebraMap R U) := Localization.basePrimeLocal_isLocalHom P Q hQP
  let : FiniteDimensional (ResidueField R) (ResidueField U) :=
    Localization.basePrimeLocal_residueFinite P Q hQP
  let : IsPurelyInseparable (RatFunc k) (RatFunc E) := RatFunc.isPurelyInseparable_ratFunc
  have hdegree : finrank (RatFunc k) (RatFunc E) = d := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq p]
  obtain ⟨hPure, hDiv, hNorm⟩ :=
    purePrimeResidue_atPrime k[X] E[X] (RatFunc k) (RatFunc E) bP bQ (hdegree.symm ▸ hp)
  let : IsPurelyInseparable (ResidueField R) (ResidueField U) := hPure
  have hDiv' : finrank (ResidueField R) (ResidueField U) ∣ d :=
    dvd_trans hDiv (dvd_of_eq hdegree)
  let σ : ResidueField R ≃+* H := (quotientRingEquivResidueField P).symm
  let ε : ResidueField U ≃+* AdjoinRoot (poly q.1.2) := (quotientRingEquivResidueField Q).symm
  let θ : AdjoinRoot (poly q.1.2) ≃+* G :=
    AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q
  let τ := ε.trans θ
  have hcoord : ε.toRingHom.comp (algebraMap (ResidueField R) (ResidueField U)) =
      (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2).comp σ.toRingHom :=
    quotientRingEquivResidueField_symm_comp_residueField_map_eq_comp_symm
      (algebraMap k E) h q.1.2 q.2
  have hστ : τ.toRingHom.comp (algebraMap (ResidueField R) (ResidueField U)) =
      (algebraMap H G).comp σ.toRingHom := by
    apply RingHom.ext
    intro a
    change θ (ε (algebraMap (ResidueField R) (ResidueField U) a)) = algebraMap H G (σ a)
    have ha : ε (algebraMap (ResidueField R) (ResidueField U) a) =
        AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2 (σ a) :=
      RingHom.congr_fun hcoord a
    rw [ha]
    exact AdjoinRoot.tensorSwapFactorQuotientEquiv_map (poly p) (poly h) q (σ a)
  let : IsPurelyInseparable H G := IsPurelyInseparable.of_equiv_equiv σ τ hστ
  let : Module.Finite H G := (monic r.1.2).finite_adjoinRoot
  have hG : finrank H G ∣ d := by
    rw [← Algebra.finrank_eq_of_equiv_equiv σ τ hστ.symm]
    exact hDiv'
  have hfin : finrank H G = r.1.1 := by
    rw [AdjoinRoot.finrank_eq_natDegree (monic r.1.2), natDegree_eq r.1.2]
  have hSimple (z : MilnorKRing G) : milnorKNormRing H G z = simpleMilnorNorm r.1.2 z := by
    let f : G ≃ₐ[H] H[X] ⧸ Ideal.span {poly r.1.2} :=
      { toRingEquiv := RingEquiv.refl _
        commutes' := fun _ ↦ rfl }
    have hf : milnorKRingMap f.toRingHom z = z := milnorKRingMap_id_apply z
    rcases (Nat.dvd_prime hp).mp hG with h1 | hpG
    · exact (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one
        r.1.2 (hfin.symm.trans h1) f z).trans (congrArg (simpleMilnorNorm r.1.2) hf)
    · exact (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
        (hpG.symm ▸ hp) r.1.2 f z).trans (congrArg (simpleMilnorNorm r.1.2) hf)
  let y := dvrMilnorTameSymbol' U (RatFunc E) n x
  have hNormRing := milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
    hp hDiv' σ τ hστ (y : MilnorKRing (ResidueField U))
  have hLower := monicIrreducibleResidue_coe_eq_canonical h n
    (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x)
  have hUpper := monicIrreducibleResidue_coe_eq_canonical q.1.2 n x
  simp only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
    milnorKTransport_coe] at hLower hUpper
  have hSquare := congrArg (fun a : MilnorKTheory (ResidueField R) n =>
    milnorKRingMap σ.toRingHom (a : MilnorKRing (ResidueField R))) (hNorm n x)
  have hBranch : milnorKRingMap τ.toRingHom (y : MilnorKRing (ResidueField U)) =
      milnorKRingMap θ.toRingHom
        (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E))) := by
    calc
      _ = milnorKRingMap θ.toRingHom
          (milnorKRingMap ε.toRingHom (y : MilnorKRing (ResidueField U))) :=
        (milnorKRingMap_comp_apply ε.toRingHom θ.toRingHom _).symm
      _ = _ := congrArg (milnorKRingMap θ.toRingHom) hUpper.symm
  exact hLower.trans (hSquare.trans (hNormRing.trans
    ((hSimple _).trans (congrArg (simpleMilnorNorm r.1.2) hBranch))))

end Stacks.Chow

end
