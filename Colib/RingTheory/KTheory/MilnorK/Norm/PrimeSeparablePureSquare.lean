/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeDiamondPure
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeResidueEquiv

import Colib.RingTheory.AdjoinRoot.TensorFactorMaps
import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivarianceAcross
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# The chosen norm square for a separable and a prime-pure extension

The coefficient image of the separable polynomial is irreducible over the
purely inseparable field. Its quotient maps onto the given compositum. The
tensor swap preserves the original separable field map to that compositum,
and chosen-norm comparisons identify both sides of the simple-norm diamond.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance primeSeparablePureSquare_irreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance primeSeparablePureSquare_finite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (monic p).finite_adjoinRoot

private theorem surjective_of_adjoin_range_eq_top
    {A B D Q : Type u} [Field A] [Field B] [Field D] [Field Q]
    [Algebra A D] [Algebra B D] (f : Q →+* D)
    (hA : ∀ a : A, algebraMap A D a ∈ f.fieldRange)
    (hB : ∀ b : B, algebraMap B D b ∈ f.fieldRange)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) : Function.Surjective f := by
  let C : IntermediateField A D := f.fieldRange.toIntermediateField hA
  have hle : adjoin A (Set.range (algebraMap B D)) ≤ C := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    exact hB b
  have htop : (⊤ : IntermediateField A D) ≤ C := hgen ▸ hle
  intro x
  have hx : x ∈ (⊤ : IntermediateField A D) := IntermediateField.mem_top
  exact RingHom.mem_fieldRange.mp (htop hx)

private theorem isPurelyInseparable_of_adjoin_range_eq_top
    {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
    [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
    [IsScalarTower K A D] [IsScalarTower K B D] [IsPurelyInseparable K B]
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) : IsPurelyInseparable A D := by
  obtain ⟨q, _⟩ := ExpChar.exists K
  let : ExpChar A q := expChar_of_injective_algebraMap (algebraMap K A).injective q
  apply isPurelyInseparable_iff_perfectClosure_eq_top.mpr
  apply top_unique
  rw [← hgen, adjoin_le_iff]
  rintro _ ⟨b, rfl⟩
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K q b
  refine (mem_perfectClosure_iff_pow_mem q).mpr ⟨n, algebraMap K A c, ?_⟩
  rw [← IsScalarTower.algebraMap_apply K A D, IsScalarTower.algebraMap_apply K B D,
    hc, map_pow]

section Coordinates

variable {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
  [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
  [IsScalarTower K A D] [IsScalarTower K B D]
  {d e : ℕ} (p : MonicIrreducibleOfDegree K d) (h : MonicIrreducibleOfDegree K e)
  (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f //
    poly q.2 ∣ (poly h).map (algebraMap K (AdjoinRoot (poly p)))})

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "Q" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "φ" => AdjoinRoot.map (algebraMap K E) (poly h)
  (poly (Sigma.snd (Subtype.val q))) (Subtype.property q)

private theorem exists_primeSeparablePureSquare_quotientEquiv
    (hq : poly q.1.2 = (poly h).map (algebraMap K E))
    (eB : B ≃ₐ[K] E) (eA : A ≃ₐ[K] H)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) :
    ∃ τ : D ≃+* Q,
      τ.toRingHom.comp (algebraMap B D) = (algebraMap E Q).comp eB.toRingHom ∧
      τ.toRingHom.comp (algebraMap A D) = RingHom.comp φ eA.toRingHom := by
  let j : E →+* D := (algebraMap B D).comp eB.symm.toRingHom
  let jA : H →ₐ[K] D := (IsScalarTower.toAlgHom K A D).comp eA.symm.toAlgHom
  have hj : j.comp (algebraMap K E) = algebraMap K D := by
    apply RingHom.ext
    intro a
    change algebraMap B D (eB.symm (algebraMap K E a)) = algebraMap K D a
    rw [eB.symm.commutes, ← IsScalarTower.algebraMap_apply K B D]
  have hrootQ : (poly q.1.2).eval₂ j (jA (AdjoinRoot.root (poly h))) = 0 := by
    rw [hq, Polynomial.eval₂_map, hj]
    change aeval (jA (AdjoinRoot.root (poly h))) (poly h) = 0
    rw [Polynomial.aeval_algHom_apply]
    have hroot : aeval (AdjoinRoot.root (poly h)) (poly h) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    exact (congrArg jA hroot).trans (map_zero jA)
  let ψ : Q →+* D := AdjoinRoot.lift j (jA (AdjoinRoot.root (poly h))) hrootQ
  have hψB (a : E) : ψ (algebraMap E Q a) = j a :=
    AdjoinRoot.lift_of hrootQ
  have hψA : ψ.comp φ = (algebraMap A D).comp eA.symm.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change ψ (φ (AdjoinRoot.of (poly h) a)) =
        algebraMap A D (eA.symm (algebraMap K H a))
      rw [eA.symm.commutes, ← IsScalarTower.algebraMap_apply K A D]
      rw [AdjoinRoot.map_of]
      exact (hψB (algebraMap K E a)).trans (RingHom.congr_fun hj a)
    · change ψ (φ (AdjoinRoot.root (poly h))) = jA (AdjoinRoot.root (poly h))
      rw [AdjoinRoot.map_root]
      exact AdjoinRoot.lift_root hrootQ
  have hψsurj : Function.Surjective ψ := by
    refine surjective_of_adjoin_range_eq_top ψ ?_ ?_ hgen
    · intro a
      exact ⟨φ (eA a), (RingHom.congr_fun hψA (eA a)).trans
        (congrArg (algebraMap A D) (eA.symm_apply_apply a))⟩
    · intro b
      exact ⟨algebraMap E Q (eB b), (hψB (eB b)).trans
        (congrArg (algebraMap B D) (eB.symm_apply_apply b))⟩
  let τ : D ≃+* Q := (RingEquiv.ofBijective ψ ⟨ψ.injective, hψsurj⟩).symm
  refine ⟨τ, ?_, ?_⟩
  · apply RingHom.ext
    intro b
    change τ (algebraMap B D b) = algebraMap E Q (eB b)
    apply τ.symm.injective
    rw [τ.symm_apply_apply]
    change algebraMap B D b = ψ (algebraMap E Q (eB b))
    rw [hψB]
    exact congrArg (algebraMap B D) (eB.symm_apply_apply b).symm
  · apply RingHom.ext
    intro a
    change τ (algebraMap A D a) = φ (eA a)
    apply τ.symm.injective
    rw [τ.symm_apply_apply]
    change algebraMap A D a = ψ (φ (eA a))
    exact ((RingHom.congr_fun hψA (eA a)).trans
      (congrArg (algebraMap A D) (eA.symm_apply_apply a))).symm

variable [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional A D]
  [FiniteDimensional B D] [Algebra.IsSeparable K A] [IsPurelyInseparable K B]

private theorem primeSeparablePureSquare_of_quotientEquiv
    [IsPurelyInseparable A D] (hp : (finrank K B).Prime) (hp₀ : d.Prime)
    (hsep : (poly h).Separable) (hq : poly q.1.2 = (poly h).map (algebraMap K E))
    (eB : B ≃ₐ[K] E) (eA : A ≃ₐ[K] H) (τ : D ≃+* Q)
    (hτB : τ.toRingHom.comp (algebraMap B D) = (algebraMap E Q).comp eB.toRingHom)
    (hτA : τ.toRingHom.comp (algebraMap A D) = RingHom.comp φ eA.toRingHom)
    (x : MilnorKRing D) :
    milnorKNormRing K B (milnorKNormRing B D x) =
      milnorKNormRing K A (milnorKNormRing A D x) := by
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  let R := AdjoinRoot (poly r.1.2)
  let s : Q ≃+* R := AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q
  let υ : D ≃+* R := τ.trans s
  have hυA : υ.toRingHom.comp (algebraMap A D) = (algebraMap H R).comp eA.toRingHom := by
    apply RingHom.ext
    intro a
    change s (τ (algebraMap A D a)) = algebraMap H R (eA a)
    have heq : τ (algebraMap A D a) = φ (eA a) := RingHom.congr_fun hτA a
    rw [heq]
    exact AdjoinRoot.tensorSwapFactorQuotientEquiv_map (poly p) (poly h) q (eA a)
  let : IsPurelyInseparable K E := eB.isPurelyInseparable
  have hqsep : (poly q.1.2).Separable := by
    rw [hq]
    exact hsep.map
  let : Algebra.IsSeparable E Q := AdjoinRoot.isSeparable_of_polynomial_separable _ hqsep
  let : Algebra.IsSeparable B D :=
    (Algebra.IsSeparable.iff_of_equiv_equiv eB.toRingEquiv τ hτB.symm).mpr inferInstance
  let : IsPurelyInseparable H R := IsPurelyInseparable.of_equiv_equiv eA.toRingEquiv υ hυA
  have hBA : finrank B D = finrank K A := by
    calc
      finrank B D = finrank E Q := Algebra.finrank_eq_of_equiv_equiv eB.toRingEquiv τ hτB.symm
      _ = (poly q.1.2).natDegree := by
        rw [(AdjoinRoot.powerBasis (ne_zero q.1.2)).finrank, AdjoinRoot.powerBasis_dim]
      _ = (poly h).natDegree := by rw [hq, Polynomial.natDegree_map]
      _ = finrank K A := by
        rw [eA.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis (ne_zero h)).finrank,
          AdjoinRoot.powerBasis_dim]
  have hdegAD : finrank A D = finrank K B := by
    apply Nat.eq_of_mul_eq_mul_left (n := finrank K A) Module.finrank_pos
    rw [Module.finrank_mul_finrank K A D, ← hBA, Nat.mul_comm, Module.finrank_mul_finrank K B D]
  have hpAD : (finrank A D).Prime := hdegAD.symm ▸ hp
  have hpHR : (finrank H R).Prime :=
    Algebra.finrank_eq_of_equiv_equiv eA.toRingEquiv υ hυA.symm ▸ hpAD
  let y : MilnorKRing Q := milnorKRingMap τ.toRingHom x
  let w : MilnorKRing R := milnorKRingMap υ.toRingHom x
  have hBnorm : milnorKRingMap eB.toRingHom (milnorKNormRing B D x) = milnorKNormRing E Q y := by
    simpa only [milnorKRingMapLift_eq] using
      milnorKNormRing_map_ringEquiv_across_of_isSeparable eB.toRingEquiv τ hτB x
  have hQnorm : milnorKNormRing E Q y = simpleMilnorNorm q.1.2 y :=
    milnorKNormRing_eq_simpleMilnorNorm_of_isSeparable q.1.2 y
  have hBcomparison :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable hp p eB
      (milnorKNormRing B D x)
  have hleft : milnorKNormRing K B (milnorKNormRing B D x) =
      simpleMilnorNorm p (simpleMilnorNorm q.1.2 y) :=
    hBcomparison.trans (congrArg (simpleMilnorNorm p) (hBnorm.trans hQnorm))
  have hAnorm : milnorKRingMap eA.toRingHom (milnorKNormRing A D x) = milnorKNormRing H R w :=
    milnorKNormRing_map_ringEquiv_of_prime_of_isPurelyInseparable hpAD eA.toRingEquiv υ hυA x
  let eR : R ≃ₐ[H] (H[X] ⧸ Ideal.span {poly r.1.2}) :=
    { toRingEquiv := RingEquiv.refl _, commutes' := fun _ => rfl }
  have hRcomparison :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable hpHR r.1.2 eR w
  change milnorKNormRing H R w = simpleMilnorNorm r.1.2 (milnorKRingMap (RingHom.id R) w)
    at hRcomparison
  have hRnorm : milnorKNormRing H R w = simpleMilnorNorm r.1.2 w := by
    simpa only [milnorKRingMap_id_apply] using hRcomparison
  have hright : milnorKNormRing K A (milnorKNormRing A D x) =
      simpleMilnorNorm h (simpleMilnorNorm r.1.2 w) :=
    (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable h eA
      (milnorKNormRing A D x)).trans (congrArg (simpleMilnorNorm h) (hAnorm.trans hRnorm))
  have hswap : milnorKRingMap s.toRingHom y = w :=
    milnorKRingMap_comp_apply τ.toRingHom s.toRingHom x
  have hdiamond := simpleMilnorNorm_prime_diamond_of_isPurelyInseparable p hp₀ h q y
  exact hleft.trans (hdiamond.trans
    ((congrArg (simpleMilnorNorm h) (congrArg (simpleMilnorNorm r.1.2) hswap)).trans hright.symm))

end Coordinates

/-- The native chosen norms of a finite separable extension and a purely
inseparable prime extension commute around their given compositum. -/
theorem milnorKNormRing_comp_of_isSeparable_of_isPurelyInseparable_prime
    {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
    [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
    [IsScalarTower K A D] [IsScalarTower K B D]
    [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional A D] [FiniteDimensional B D]
    [Algebra.IsSeparable K A] [IsPurelyInseparable K B] (hp : (finrank K B).Prime)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) (x : MilnorKRing D) :
    milnorKNormRing K B (milnorKNormRing B D x) =
      milnorKNormRing K A (milnorKNormRing A D x) := by
  obtain ⟨b, _, eB₀, hbdeg, _⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime (K := K) (L := B) hp
  let p := minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) b)
  let E := AdjoinRoot (poly p)
  let eB : B ≃ₐ[K] E := eB₀
  let : IsPurelyInseparable K E := eB.isPurelyInseparable
  have hp₀ : (minpoly K b).natDegree.Prime := hbdeg.symm ▸ hp
  obtain ⟨e, h, ⟨eA⟩⟩ := exists_monicIrreducible_presentation K A
  let : Algebra.IsSeparable K (AdjoinRoot (poly h)) := AlgEquiv.Algebra.isSeparable eA
  have hsep : (poly h).Separable := AdjoinRoot.polynomial_separable_of_isSeparable _ (monic h)
  let q₀ : MonicIrreducibleOfDegree E e :=
    ⟨(poly h).map (algebraMap K E), (monic h).map _,
      hsep.map_irreducible_of_isPurelyInseparable E (irreducible h),
      by rw [Polynomial.natDegree_map, natDegree_eq h]⟩
  let q : {q : Σ d : ℕ, MonicIrreducibleOfDegree E d //
      poly q.2 ∣ (poly h).map (algebraMap K E)} := ⟨⟨e, q₀⟩, dvd_rfl⟩
  have hq : poly q.1.2 = (poly h).map (algebraMap K E) := rfl
  obtain ⟨τ, hτB, hτA⟩ := exists_primeSeparablePureSquare_quotientEquiv p h q hq eB eA hgen
  let : IsPurelyInseparable A D := isPurelyInseparable_of_adjoin_range_eq_top (K := K) hgen
  exact primeSeparablePureSquare_of_quotientEquiv p h q hp hp₀ hsep hq eB eA τ hτB hτA x

end Stacks.Chow

end
