/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PurelyInseparable.NormalPrimePower
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeNormalDiamondCoherence
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenRecursion
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeEquivariance
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable

/-!
# Chosen-norm degree induction with native prime coherence

The induction retains the actual first witness selected by the original chosen
norm. Its simple norm is factored through a prime subfield, and the two-prime
diamond compares that field with the specified prime field. All remaining
chosen norms occur over bases with strictly smaller top-field degree.

The input-form lemmas keep the prime field-coordinate identities explicit.
The final pure endpoints instantiate them with the native polynomial proofs.
Nothing here cancels a characteristic-power scalar in a Milnor group.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

private instance chosenPrimePower_nativeIrreducible {K : Type u} [Field K]
    {d : ℕ} (q : MonicIrreducibleOfDegree K d) : Fact (Irreducible (poly q)) :=
  ⟨irreducible q⟩

/-- Chosen/simple comparison in every actual presentation of this extension. -/
def NativeSimpleNormComparison (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ∀ {d : ℕ} (q : MonicIrreducibleOfDegree K d)
    (g : L ≃ₐ[K] AdjoinRoot (poly q)) (x : MilnorKRing L),
    milnorKNormRing K L x = simpleMilnorNorm q (milnorKRingMap g.toRingHom x)

/-- Native tower compatibility through every actual finite intermediate field. -/
def NativeNormTowerProperty (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ∀ (M : Type u) [Field M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] (x : MilnorKRing L),
    milnorKNormRing K M (milnorKNormRing M L x) = milnorKNormRing K L x

/-- Simultaneous field-isomorphism naturality, retaining both original algebra maps. -/
def NativeNormNaturalityProperty (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ∀ (K' L' : Type u) [Field K'] [Field L'] [Algebra K' L']
    [FiniteDimensional K' L'] (σ : K ≃+* K') (τ : L ≃+* L'),
    τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom →
    ∀ x : MilnorKRing L,
      milnorKRingMap σ.toRingHom (milnorKNormRing K L x) =
        milnorKNormRing K' L' (milnorKRingMap τ.toRingHom x)

private theorem chosenPrimePower_compare_of_bijective
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hb : Function.Bijective (algebraMap K L)) {d : ℕ}
    (q : MonicIrreducibleOfDegree K d) (f : L ≃ₐ[K] AdjoinRoot (poly q))
    (x : MilnorKRing L) :
    milnorKNormRing K L x = simpleMilnorNorm q (milnorKRingMap f.toRingHom x) := by
  let b : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) hb
  have hdim : finrank K L = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hb
  have hd : d = 1 := by
    calc
      d = (poly q).natDegree := (natDegree_eq q).symm
      _ = finrank K (AdjoinRoot (poly q)) := finrank_quotient_span_eq_natDegree.symm
      _ = finrank K L := f.toLinearEquiv.finrank_eq.symm
      _ = 1 := hdim
  subst d
  let g : AdjoinRoot (poly q) ≃ₐ[K] K := f.symm.trans b.symm
  have hchosen := milnorKNormRing_of_bijective hb x
  have hsimple := simpleMilnorNorm_eq_map_of_degree_one q g (milnorKRingMap f.toRingHom x)
  have hcomp := milnorKRingMap_comp_apply f.toRingHom g.toRingHom x
  have hg : g.toRingHom.comp f.toRingHom =
      (RingEquiv.ofBijective (algebraMap K L) hb).symm.toRingHom := by
    apply RingHom.ext
    intro z
    change b.symm (f.symm (f z)) = b.symm z
    rw [f.symm_apply_apply]
  have hmaps := congrArg (fun ψ : L →+* K => milnorKRingMap ψ x) hg
  exact hchosen.trans (hsimple.trans (hcomp.trans hmaps)).symm

/-- The induction step factors the original chosen norm through any specified
pure prime field. Both relative-degree-one branches of the diamond are retained. -/
theorem milnorKNormRing_factor_prime_of_smaller_pure_coherence
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p) (n : ℕ)
    (hcomparison : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeSimpleNormComparison A B)
    (htower : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeNormTowerProperty A B)
    (K P L : Type u) [Field K] [Field P] [Field L] [CharP K p]
    [Algebra K P] [Algebra P L] [Algebra K L] [IsScalarTower K P L]
    [FiniteDimensional K P] [FiniteDimensional P L] [FiniteDimensional K L]
    [IsPurelyInseparable K L]
    (hP : finrank K P = p) (hn : finrank K L = n) (x : MilnorKRing L) :
    milnorKNormRing K L x = milnorKNormRing K P (milnorKNormRing P L x) := by
  classical
  have hp : p.Prime := Fact.out
  let : IsPurelyInseparable K P := IsPurelyInseparable.tower_bot K P L
  let : IsPurelyInseparable P L := IsPurelyInseparable.tower_top K P L
  let : CharP P p := charP_of_injective_algebraMap (algebraMap K P).injective p
  have hPLlt : finrank P L < n := by
    rw [← hn, ← finrank_mul_finrank K P L, hP]
    exact lt_mul_of_one_lt_left finrank_pos hp.one_lt
  have hLone : 1 < finrank K L := by
    rw [← finrank_mul_finrank K P L, hP]
    exact lt_of_lt_of_le hp.one_lt
      (Nat.le_mul_of_pos_right p (finrank_pos (R := P) (M := L)))
  have h : ∃ a : L, a ∉ Set.range (algebraMap K L) := by
    by_contra h
    have hb := bijective_algebraMap_of_forall h
    exact (Nat.ne_of_gt hLone) (Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hb)
  let a : L := h.choose
  let A := K⟮a⟯
  let : FiniteDimensional K A := FiniteDimensional.left K A L
  let : FiniteDimensional A L := FiniteDimensional.right K A L
  let : IsPurelyInseparable K A := IsPurelyInseparable.tower_bot K A L
  have hAone : 1 < finrank K A := by
    apply lt_of_le_of_ne (Nat.succ_le_of_lt (finrank_pos (R := K) (M := A)))
    intro heq
    exact h.choose_spec (finrank_adjoin_simple_eq_one_iff.mp heq.symm)
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K A p
  obtain ⟨Q, hQnormal, hQ⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
      p r hr (AlgHom.id K A) hAone
  let : Normal K Q := hQnormal
  let : FiniteDimensional K Q := FiniteDimensional.left K Q A
  let : FiniteDimensional Q A := FiniteDimensional.right K Q A
  let : IsPurelyInseparable K Q := IsPurelyInseparable.tower_bot K Q A
  let : IsScalarTower Q A L := inferInstance
  let : IsScalarTower K Q L := inferInstance
  let : FiniteDimensional Q L := FiniteDimensional.right K Q L
  let : IsPurelyInseparable Q A := IsPurelyInseparable.tower_top K Q A
  let : IsPurelyInseparable Q L := IsPurelyInseparable.tower_top K Q L
  let : CharP Q p := charP_of_injective_algebraMap (algebraMap K Q).injective p
  have hQLlt : finrank Q L < n := by
    rw [← hn, ← finrank_mul_finrank K Q L, hQ]
    exact lt_mul_of_one_lt_left finrank_pos hp.one_lt
  have hQAlt : finrank Q A < n := by
    apply lt_of_le_of_lt _ hQLlt
    rw [← finrank_mul_finrank Q A L]
    exact Nat.le_mul_of_pos_right _ (finrank_pos (R := A) (M := L))
  let ha : IsIntegral K a := Algebra.IsIntegral.isIntegral (R := K) a
  let qA := minpolyOfDegree K ha
  let eA := adjoinSimpleEquivQuot K ha
  obtain ⟨d, q, g, hsimple⟩ := hfactor K Q A hQ qA eA
  have hsimpleNative (z : MilnorKRing A) :
      milnorKNormAdjoinSimple K ha z =
        milnorKNormRing K Q (simpleMilnorNorm q (milnorKRingMap g.toRingHom z)) :=
    hsimple z
  have hcompare := hcomparison Q A hQAlt q g (milnorKNormRing A L x)
  have hrelative := htower Q L hQLlt A x
  have hselected : milnorKNormRing K L x =
      milnorKNormRing K Q (milnorKNormRing Q L x) := by
    have hfirst := milnorKNormRing_selected_step_apply h x
    exact hfirst.trans ((hsimpleNative _).trans
      (congrArg (milnorKNormRing K Q) (hcompare.symm.trans hrelative)))
  let C := IntermediateField.adjoin P (Set.range (algebraMap Q L))
  let : Algebra Q C := (adjoinRangeFactor Q P L).toAlgebra
  let : IsScalarTower Q C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FiniteDimensional P C :=
    finiteDimensional_adjoin_range_of_finiteDimensional K Q P L
  let : FiniteDimensional Q C := FiniteDimensional.left Q C L
  let : FiniteDimensional C L := FiniteDimensional.right P C L
  have hPtop := htower P L hPLlt C x
  have hQtop := htower Q L hQLlt C x
  have hcommute := hdiamond K P Q L hP hQ (milnorKNormRing C L x)
  calc
    milnorKNormRing K L x = milnorKNormRing K Q (milnorKNormRing Q L x) := hselected
    _ = milnorKNormRing K Q (milnorKNormRing Q C (milnorKNormRing C L x)) :=
      congrArg (milnorKNormRing K Q) hQtop.symm
    _ = milnorKNormRing K P (milnorKNormRing P C (milnorKNormRing C L x)) :=
      hcommute.symm
    _ = milnorKNormRing K P (milnorKNormRing P L x) :=
      congrArg (milnorKNormRing K P) hPtop

/-- At the current degree, prime factorization and smaller comparison/tower
cases identify the chosen norm in every actual simple presentation. -/
theorem nativeSimpleNormComparison_of_smaller_pure_coherence
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p) (n : ℕ)
    (hcomparison : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeSimpleNormComparison A B)
    (htower : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeNormTowerProperty A B)
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] [CharP K p]
    (hn : finrank K L = n) : NativeSimpleNormComparison K L := by
  intro d q g x
  classical
  by_cases hb : Function.Bijective (algebraMap K L)
  · exact chosenPrimePower_compare_of_bijective hb q g x
  have hLone : 1 < finrank K L := by
    apply lt_of_le_of_ne (Nat.succ_le_of_lt (finrank_pos (R := K) (M := L)))
    intro heq
    exact hb (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp heq.symm)
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K L p
  obtain ⟨P, hPnormal, hP⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
      p r hr (AlgHom.id K L) hLone
  let : Normal K P := hPnormal
  let : FiniteDimensional K P := FiniteDimensional.left K P L
  let : FiniteDimensional P L := FiniteDimensional.right K P L
  let : IsPurelyInseparable P L := IsPurelyInseparable.tower_top K P L
  let : CharP P p := charP_of_injective_algebraMap (algebraMap K P).injective p
  have hPLlt : finrank P L < n := by
    rw [← hn, ← finrank_mul_finrank K P L, hP]
    exact lt_mul_of_one_lt_left finrank_pos (Fact.out : p.Prime).one_lt
  obtain ⟨e, r, f, hsimple⟩ := hfactor K P L hP q g
  have hrelative := hcomparison P L hPLlt r f x
  have hfirst := milnorKNormRing_factor_prime_of_smaller_pure_coherence
    p hfactor hdiamond n hcomparison htower K P L hP hn x
  exact hfirst.trans ((congrArg (milnorKNormRing K P) hrelative).trans (hsimple x).symm)

private theorem chosenPrimePower_naturality_of_bijective
    {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    (hb : Function.Bijective (algebraMap K L)) (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) =
      (algebraMap K' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing K L x) =
      milnorKNormRing K' L' (milnorKRingMap τ.toRingHom x) := by
  have hcoord (a : K) : τ (algebraMap K L a) = algebraMap K' L' (σ a) :=
    RingHom.congr_fun hστ a
  have hb' : Function.Bijective (algebraMap K' L') := by
    refine ⟨(algebraMap K' L').injective, ?_⟩
    intro y
    obtain ⟨z, rfl⟩ := τ.surjective y
    obtain ⟨a, rfl⟩ := hb.surjective z
    exact ⟨σ a, (hcoord a).symm⟩
  let e := RingEquiv.ofBijective (algebraMap K L) hb
  let e' := RingEquiv.ofBijective (algebraMap K' L') hb'
  have hmap : σ.toRingHom.comp e.symm.toRingHom = e'.symm.toRingHom.comp τ.toRingHom := by
    apply RingHom.ext
    intro z
    apply e'.injective
    change e' (σ (e.symm z)) = e' (e'.symm (τ z))
    rw [e'.apply_symm_apply]
    change algebraMap K' L' (σ (e.symm z)) = τ z
    rw [← hcoord]
    exact congrArg τ (e.apply_symm_apply z)
  rw [milnorKNormRing_of_bijective hb, milnorKNormRing_of_bijective hb',
    milnorKRingMap_comp_apply, milnorKRingMap_comp_apply]
  exact congrArg (fun f : L →+* K' => milnorKRingMap f x) hmap

/-- The current-degree naturality square reduces through a common actual prime
field. The relative norm comparison uses only strictly smaller degree. -/
theorem nativeNormNaturality_of_smaller_pure_coherence
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p) (n : ℕ)
    (hcomparison : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeSimpleNormComparison A B)
    (htower : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeNormTowerProperty A B)
    (hnaturality : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeNormNaturalityProperty A B)
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] [CharP K p]
    (hn : finrank K L = n) : NativeNormNaturalityProperty K L := by
  intro K' L' _ _ _ _ σ τ hστ x
  classical
  by_cases hb : Function.Bijective (algebraMap K L)
  · exact chosenPrimePower_naturality_of_bijective hb σ τ hστ x
  let : Algebra K K' := σ.toRingHom.toAlgebra
  let : FiniteDimensional K K' :=
    Module.Finite.of_surjective (Algebra.linearMap K K') σ.surjective
  have hKK' : finrank K K' = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr σ.bijective
  let : Algebra K L' := ((algebraMap K' L').comp σ.toRingHom).toAlgebra
  have : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L' := Module.Finite.trans K' L'
  let τK : L ≃ₐ[K] L' :=
    { toRingEquiv := τ
      commutes' := fun a => RingHom.congr_fun hστ a }
  let : IsPurelyInseparable K L' := τK.isPurelyInseparable
  let : IsPurelyInseparable K' L' := IsPurelyInseparable.tower_top K K' L'
  let : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  have hn' : finrank K' L' = n := by
    have h := finrank_mul_finrank K K' L'
    rw [hKK', one_mul] at h
    exact h.trans (τK.toLinearEquiv.finrank_eq.symm.trans hn)
  have hLone : 1 < finrank K L := by
    apply lt_of_le_of_ne (Nat.succ_le_of_lt (finrank_pos (R := K) (M := L)))
    intro heq
    exact hb (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp heq.symm)
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K L p
  obtain ⟨P, hPnormal, hP⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
      p r hr (AlgHom.id K L) hLone
  let : Normal K P := hPnormal
  let : FiniteDimensional K P := FiniteDimensional.left K P L
  let : FiniteDimensional P L := FiniteDimensional.right K P L
  let : IsPurelyInseparable K P := IsPurelyInseparable.tower_bot K P L
  let : IsPurelyInseparable P L := IsPurelyInseparable.tower_top K P L
  let : CharP P p := charP_of_injective_algebraMap (algebraMap K P).injective p
  have hPLlt : finrank P L < n := by
    rw [← hn, ← finrank_mul_finrank K P L, hP]
    exact lt_mul_of_one_lt_left finrank_pos (Fact.out : p.Prime).one_lt
  let : Algebra K' P := ((algebraMap K P).comp σ.symm.toRingHom).toAlgebra
  have : IsScalarTower K K' P := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K P a = algebraMap K P (σ.symm (σ a))
    rw [σ.symm_apply_apply]
  let : FiniteDimensional K' P := FiniteDimensional.right K K' P
  let : IsPurelyInseparable K' P := IsPurelyInseparable.tower_top K K' P
  have hP' : finrank K' P = p := by
    have h := finrank_mul_finrank K K' P
    rw [hKK', one_mul] at h
    exact h.trans hP
  let : Algebra P L' := (τ.toRingHom.comp (algebraMap P L)).toAlgebra
  have : IsScalarTower K' P L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K' L' a = τ (algebraMap P L (algebraMap K P (σ.symm a)))
    rw [← IsScalarTower.algebraMap_apply K P L]
    have h : τ (algebraMap K L (σ.symm a)) =
        algebraMap K' L' (σ (σ.symm a)) := RingHom.congr_fun hστ (σ.symm a)
    exact (congrArg (algebraMap K' L') (σ.apply_symm_apply a)).symm.trans h.symm
  let : FiniteDimensional P L' := FiniteDimensional.right K' P L'
  let : IsPurelyInseparable P L' := IsPurelyInseparable.tower_top K' P L'
  have hrel : τ.toRingHom.comp (algebraMap P L) =
      (algebraMap P L').comp (RingEquiv.refl P).toRingHom := by
    ext a
    rfl
  have hrelative : milnorKNormRing P L x =
      milnorKNormRing P L' (milnorKRingMap τ.toRingHom x) := by
    have h := hnaturality P L hPLlt P L' (RingEquiv.refl P) τ hrel x
    change milnorKRingMap (RingHom.id P) (milnorKNormRing P L x) = _ at h
    rw [milnorKRingMap_id_apply] at h
    exact h
  have houter : (RingEquiv.refl P).toRingHom.comp (algebraMap K P) =
      (algebraMap K' P).comp σ.toRingHom := by
    apply RingHom.ext
    intro a
    change algebraMap K P a = algebraMap K P (σ.symm (σ a))
    rw [σ.symm_apply_apply]
  have hprime : milnorKRingMap σ.toRingHom
      (milnorKNormRing K P (milnorKNormRing P L x)) =
        milnorKNormRing K' P (milnorKNormRing P L x) := by
    have h := milnorKNormRing_map_ringEquiv_of_prime_of_isPurelyInseparable
      (hP.symm ▸ (Fact.out : p.Prime)) σ (RingEquiv.refl P) houter
      (milnorKNormRing P L x)
    change _ = milnorKNormRing K' P
      (milnorKRingMap (RingHom.id P) (milnorKNormRing P L x)) at h
    rw [milnorKRingMap_id_apply] at h
    exact h
  have hsource := milnorKNormRing_factor_prime_of_smaller_pure_coherence
    p hfactor hdiamond n hcomparison htower K P L hP hn x
  have htarget := milnorKNormRing_factor_prime_of_smaller_pure_coherence
    p hfactor hdiamond n hcomparison htower K' P L' hP' hn'
      (milnorKRingMap τ.toRingHom x)
  exact (congrArg (milnorKRingMap σ.toRingHom) hsource).trans
    (hprime.trans ((congrArg (milnorKNormRing K' P) hrelative).trans htarget.symm))

/-- The current-degree tower step uses naturality for the genuine degree-one
endpoints and prime factorization for every proper nontrivial intermediate field. -/
theorem nativeNormTowerProperty_of_smaller_pure_coherence
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p) (n : ℕ)
    (hcomparison : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeSimpleNormComparison A B)
    (htower : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
      finrank A B < n → NativeNormTowerProperty A B)
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] [CharP K p]
    (hn : finrank K L = n) (hnat : NativeNormNaturalityProperty K L) :
    NativeNormTowerProperty K L := by
  intro M _ _ _ _ _ _ x
  classical
  let : IsPurelyInseparable K M := IsPurelyInseparable.tower_bot K M L
  let : IsPurelyInseparable M L := IsPurelyInseparable.tower_top K M L
  let : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  by_cases hKM : finrank K M = 1
  · have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hKM
    let σ := RingEquiv.ofBijective (algebraMap K M) hb
    have hσ : (RingEquiv.refl L).toRingHom.comp (algebraMap K L) =
        (algebraMap M L).comp σ.toRingHom := by
      ext a
      exact IsScalarTower.algebraMap_apply K M L a
    have h := hnat M L σ (RingEquiv.refl L) hσ x
    change milnorKRingMap (algebraMap K M) (milnorKNormRing K L x) =
      milnorKNormRing M L (milnorKRingMap (RingHom.id L) x) at h
    rw [milnorKRingMap_id_apply] at h
    have h' := congrArg (milnorKNormRing K M) h
    rw [milnorKNormRing_milnorKRingMap, hKM, Nat.cast_one, one_smul] at h'
    exact h'.symm
  by_cases hML : finrank M L = 1
  · have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hML
    let τ := RingEquiv.ofBijective (algebraMap M L) hb
    have hτ : τ.symm.toRingHom.comp (algebraMap K L) =
        (algebraMap K M).comp (RingEquiv.refl K).toRingHom := by
      ext a
      change τ.symm (algebraMap K L a) = algebraMap K M a
      rw [IsScalarTower.algebraMap_apply K M L]
      exact τ.symm_apply_apply (algebraMap K M a)
    have h := hnat K M (RingEquiv.refl K) τ.symm hτ x
    change milnorKRingMap (RingHom.id K) (milnorKNormRing K L x) =
      milnorKNormRing K M (milnorKRingMap τ.symm.toRingHom x) at h
    rw [milnorKRingMap_id_apply] at h
    rw [milnorKNormRing_of_bijective hb]
    exact h.symm
  have hMone : 1 < finrank K M :=
    lt_of_le_of_ne (Nat.succ_le_of_lt (finrank_pos (R := K) (M := M)))
      (fun h => hKM h.symm)
  have hMLone : 1 < finrank M L :=
    lt_of_le_of_ne (Nat.succ_le_of_lt (finrank_pos (R := M) (M := L)))
      (fun h => hML h.symm)
  have hMlt : finrank K M < n := by
    rw [← hn, ← finrank_mul_finrank K M L]
    exact lt_mul_of_one_lt_right finrank_pos hMLone
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K M p
  obtain ⟨P, hPnormal, hP⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
      p r hr (AlgHom.id K M) hMone
  let : Normal K P := hPnormal
  let : FiniteDimensional K P := FiniteDimensional.left K P M
  let : FiniteDimensional P M := FiniteDimensional.right K P M
  let : IsScalarTower P M L := inferInstance
  let : IsScalarTower K P L := inferInstance
  let : FiniteDimensional P L := FiniteDimensional.right K P L
  let : IsPurelyInseparable P L := IsPurelyInseparable.tower_top K P L
  let : CharP P p := charP_of_injective_algebraMap (algebraMap K P).injective p
  have hPLlt : finrank P L < n := by
    rw [← hn, ← finrank_mul_finrank K P L, hP]
    exact lt_mul_of_one_lt_left finrank_pos (Fact.out : p.Prime).one_lt
  have hlower := htower K M hMlt P (milnorKNormRing M L x)
  have hupper := htower P L hPLlt M x
  have hroot := milnorKNormRing_factor_prime_of_smaller_pure_coherence
    p hfactor hdiamond n hcomparison htower K P L hP hn x
  exact hlower.symm.trans ((congrArg (milnorKNormRing K P) hupper).trans hroot.symm)

/-- Simultaneous strong degree induction for the actual finite pure norm:
all simple presentations, simultaneous field isomorphisms, and arbitrary
intermediate fields. The two prime coherence inputs remain explicit. -/
theorem native_pure_norm_coherence_of_prime_inputs
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p) :
    ∀ (n : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsPurelyInseparable K L] [CharP K p],
      finrank K L = n → NativeSimpleNormComparison K L ∧
        NativeNormNaturalityProperty K L ∧ NativeNormTowerProperty K L := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcomparison : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
        [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
        finrank A B < n → NativeSimpleNormComparison A B := by
      intro A B _ _ _ _ _ _ hlt
      exact (ih (finrank A B) hlt A B rfl).1
    have htower : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
        [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
        finrank A B < n → NativeNormTowerProperty A B := by
      intro A B _ _ _ _ _ _ hlt
      exact (ih (finrank A B) hlt A B rfl).2.2
    have hnaturality : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
        [FiniteDimensional A B] [IsPurelyInseparable A B] [CharP A p],
        finrank A B < n → NativeNormNaturalityProperty A B := by
      intro A B _ _ _ _ _ _ hlt
      exact (ih (finrank A B) hlt A B rfl).2.1
    intro K L _ _ _ _ _ _ hn
    have hcompare : NativeSimpleNormComparison K L :=
      nativeSimpleNormComparison_of_smaller_pure_coherence
      p hfactor hdiamond n hcomparison htower K L hn
    have hnatural : NativeNormNaturalityProperty K L :=
      nativeNormNaturality_of_smaller_pure_coherence
      p hfactor hdiamond n hcomparison htower hnaturality K L hn
    have htower' : NativeNormTowerProperty K L :=
      nativeNormTowerProperty_of_smaller_pure_coherence
      p hfactor hdiamond n hcomparison htower K L hn hnatural
    exact ⟨hcompare, hnatural, htower'⟩

/-- Native pure transitivity from the explicit prime tower and diamond inputs. -/
theorem milnorKNormRing_tower_of_isPurelyInseparable_of_prime_inputs
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p)
    {K M L : Type u} [Field K] [Field M] [Field L] [CharP K p]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (x : MilnorKRing L) :
    milnorKNormRing K M (milnorKNormRing M L x) = milnorKNormRing K L x :=
  (native_pure_norm_coherence_of_prime_inputs p hfactor hdiamond
    (finrank K L) K L rfl).2.2 M x

/-- Native pure naturality from the same explicit prime coherence inputs. -/
theorem milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_prime_inputs
    (p : ℕ) [Fact p.Prime]
    (hfactor : NativePrimeSimpleNormFactorization.{u} p)
    (hdiamond : NativePurePrimeNormDiamond.{u} p)
    {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L'] [CharP K p]
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    [IsPurelyInseparable K L] (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) =
      (algebraMap K' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing K L x) =
      milnorKNormRing K' L' (milnorKRingMap τ.toRingHom x) :=
  (native_pure_norm_coherence_of_prime_inputs p hfactor hdiamond
    (finrank K L) K L rfl).2.1 K' L' σ τ hστ x

/-- The chosen norm agrees with the native simple norm in every actual
presentation of a finite purely inseparable extension. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isPurelyInseparable
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] {d : ℕ} (q : MonicIrreducibleOfDegree K d)
    (g : L ≃ₐ[K] AdjoinRoot (poly q)) (x : MilnorKRing L) :
    milnorKNormRing K L x = simpleMilnorNorm q (milnorKRingMap g.toRingHom x) := by
  rcases expChar_is_prime_or_one K (ringExpChar K) with hp | hzero
  · let : Fact (ringExpChar K).Prime := ⟨hp⟩
    let : CharP K (ringExpChar K) := (expChar_prime_iff K hp).mp inferInstance
    exact (native_pure_norm_coherence_of_prime_inputs (ringExpChar K)
      (nativePrimeSimpleNormFactorization _) (nativePurePrimeNormDiamond _)
      (finrank K L) K L rfl).1 q g x
  · let : ExpChar K 1 := hzero ▸ (inferInstance : ExpChar K (ringExpChar K))
    let : CharZero K := charZero_of_expChar_one' K
    let : Algebra.IsSeparable K L := inferInstance
    exact chosenPrimePower_compare_of_bijective
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L) q g x

/-- Native whole-ring norm transitivity for every finite purely inseparable
tower. The intermediate and top extensions need not be simple. -/
theorem milnorKNormRing_tower_of_isPurelyInseparable
    {K M L : Type u} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (x : MilnorKRing L) :
    milnorKNormRing K M (milnorKNormRing M L x) = milnorKNormRing K L x := by
  rcases expChar_is_prime_or_one K (ringExpChar K) with hp | hzero
  · let : Fact (ringExpChar K).Prime := ⟨hp⟩
    let : CharP K (ringExpChar K) := (expChar_prime_iff K hp).mp inferInstance
    exact milnorKNormRing_tower_of_isPurelyInseparable_of_prime_inputs
      (ringExpChar K) (nativePrimeSimpleNormFactorization _) (nativePurePrimeNormDiamond _) x
  · let : ExpChar K 1 := hzero ▸ (inferInstance : ExpChar K (ringExpChar K))
    let : CharZero K := charZero_of_expChar_one' K
    let : Algebra.IsSeparable K L := inferInstance
    exact milnorKNormRing_tower_of_isSeparable x

/-- Simultaneous field-isomorphism naturality for every finite pure chosen
norm, with the original algebra maps retained on both sides. -/
theorem milnorKNormRing_map_ringEquiv_of_isPurelyInseparable
    {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    [IsPurelyInseparable K L] (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) =
      (algebraMap K' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing K L x) =
      milnorKNormRing K' L' (milnorKRingMap τ.toRingHom x) := by
  rcases expChar_is_prime_or_one K (ringExpChar K) with hp | hzero
  · let : Fact (ringExpChar K).Prime := ⟨hp⟩
    let : CharP K (ringExpChar K) := (expChar_prime_iff K hp).mp inferInstance
    exact milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_prime_inputs
      (ringExpChar K) (nativePrimeSimpleNormFactorization _) (nativePurePrimeNormDiamond _)
      σ τ hστ x
  · let : ExpChar K 1 := hzero ▸ (inferInstance : ExpChar K (ringExpChar K))
    let : CharZero K := charZero_of_expChar_one' K
    let : Algebra.IsSeparable K L := inferInstance
    exact chosenPrimePower_naturality_of_bijective
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L) σ τ hστ x

/-- Every actual simple first step is compatible with the chosen pure norm.
The statement applies to an arbitrary element, not only the selected witness. -/
theorem milnorKNormRing_adjoinSimple_step_of_isPurelyInseparable
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (a : L) (ha : IsIntegral K a) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K ha (milnorKNormRing K⟮a⟯ L x) = milnorKNormRing K L x := by
  let A := K⟮a⟯
  let : FiniteDimensional K A := FiniteDimensional.left K A L
  let : FiniteDimensional A L := FiniteDimensional.right K A L
  let : IsPurelyInseparable K A := IsPurelyInseparable.tower_bot K A L
  have hcompare := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isPurelyInseparable
    (minpolyOfDegree K ha) (adjoinSimpleEquivQuot K ha) (milnorKNormRing A L x)
  change milnorKNormRing K A (milnorKNormRing A L x) =
    milnorKNormAdjoinSimple K ha (milnorKNormRing A L x) at hcompare
  exact hcompare.symm.trans (milnorKNormRing_tower_of_isPurelyInseparable x)

/-- The unconditional pure tower law on every native homogeneous Milnor group. -/
theorem milnorKNorm_tower_of_isPurelyInseparable
    {K M L : Type u} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm K M n (milnorKNorm M L n x) = milnorKNorm K L n x := by
  apply Subtype.ext
  exact milnorKNormRing_tower_of_isPurelyInseparable (x : MilnorKRing L)

end Stacks.Chow

end
