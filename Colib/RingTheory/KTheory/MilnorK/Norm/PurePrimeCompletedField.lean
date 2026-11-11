/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.FractionBranches
public import Colib.RingTheory.Localization.DedekindBranches
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeScalarBaseChange
public import StacksFrontier.RingTheory.BaseChangeTransport

/-!
# The actual completed fraction field of a purely inseparable extension

A powered integral element comes from the integrally closed lower ring.
This identifies every original prime over the fixed prime. The native
completed tensor product therefore has its single actual field coordinate.
-/

@[expose] public noncomputable section

open IsLocalRing Module Polynomial IntermediateField
open scoped TensorProduct

universe u

namespace Stacks.Chow

private theorem subsingleton_primesOver_of_isPurelyInseparable
    (R S F E : Type u) [CommRing R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [Algebra F E] [IsScalarTower R F E] [IsPurelyInseparable F E] (m : Ideal R) :
    Subsingleton (m.primesOver S) := by
  obtain ⟨p, _⟩ := ExpChar.exists F
  refine ⟨fun q q' => Subtype.ext (Ideal.ext fun s => ?_)⟩
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem F p (algebraMap S E s)
  have hsInt : IsIntegral R (algebraMap S E s) :=
    (Algebra.IsIntegral.isIntegral (R := R) s).map (IsScalarTower.toAlgHom R S E)
  have hbIntE : IsIntegral R (algebraMap F E b) := by
    rw [hb]
    exact hsInt.pow _
  have hbInt : IsIntegral R b := hbIntE.tower_bot (algebraMap F E).injective
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbInt
  have heq : algebraMap R S r = s ^ (p ^ n) := by
    apply IsFractionRing.injective S E
    rw [← IsScalarTower.algebraMap_apply R S E, map_pow,
      IsScalarTower.algebraMap_apply R F E, hr, hb]
  have hmem (Q : m.primesOver S) : s ∈ Q.val ↔ r ∈ m := by
    have hQ : Ideal.comap (algebraMap R S) Q.val = m := Q.property.2.over.symm
    calc
      s ∈ Q.val ↔ s ^ (p ^ n) ∈ Q.val :=
        (Q.property.1.pow_mem_iff_mem _ (pow_pos (Nat.pos_of_ne_zero
          (expChar_ne_zero F p)) n)).symm
      _ ↔ algebraMap R S r ∈ Q.val := by rw [heq]
      _ ↔ r ∈ m := Iff.of_eq (congrArg (fun J : Ideal R => r ∈ J) hQ)
  exact (hmem q).trans (hmem q').symm

/-- Pure inseparability is preserved by scalar extension to a field tensor product. -/
theorem isPurelyInseparable_of_completedTensorEquiv
    (F E B D : Type u) [Field F] [Field E] [Field B] [Field D]
    [Algebra F E] [Algebra F B] [Algebra B D] [IsPurelyInseparable F E]
    (η : B ⊗[F] E ≃ₐ[B] D) : IsPurelyInseparable B D := by
  let p := ringExpChar F
  let : ExpChar B p := expChar_of_injective_algebraMap (algebraMap F B).injective p
  apply (isPurelyInseparable_iff_pow_mem B p).mpr
  intro z
  obtain ⟨n, b, hb⟩ :=
    IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
      (k := F) (K := E) (R := B) p (η.symm z)
  refine ⟨n, b, ?_⟩
  have h := congrArg η hb
  simpa only [map_pow, η.commutes, η.apply_symm_apply] using h

/-- A field-valued tensor product preserves the original chosen norm for
a purely inseparable prime extension. -/
theorem milnorKNorm_baseChange_of_prime_of_isPurelyInseparable_of_tensorField
    (F E B D : Type u) [Field F] [Field E] [Field B] [Field D]
    [Algebra F E] [Algebra F B] [Algebra F D] [Algebra E D] [Algebra B D]
    [IsScalarTower F E D] [IsScalarTower F B D]
    [FiniteDimensional F E] [FiniteDimensional B D] [IsPurelyInseparable F E]
    (η : B ⊗[F] E ≃ₐ[B] D)
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E n) :
    milnorKTheoryMap (algebraMap F B) n (milnorKNorm F E n x) =
      milnorKNorm B D n (milnorKTheoryMap (algebraMap E D) n x) := by
  have hdegree : finrank B D = finrank F E :=
    η.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange
  obtain ⟨a, ha, e, _, _⟩ := exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let f : F[X] := minpoly F a
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := F) a)
  let fD : B[X] := f.map (algebraMap F B)
  let e0 : E ≃ₐ[F] AdjoinRoot f := e
  let eB : B ⊗[F] E ≃+* AdjoinRoot fD :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) e0).toRingEquiv.trans
      (AdjoinRoot.baseChangeAlgEquiv F B f).toRingEquiv
  let g : AdjoinRoot fD ≃+* D := eB.symm.trans η.toRingEquiv
  have hdom : IsDomain (AdjoinRoot fD) := Function.Injective.isDomain g.toRingHom g.injective
  have hprime : (Ideal.span ({fD} : Set B[X])).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hirr : Irreducible fD :=
    ((Ideal.span_singleton_prime (hf.map (algebraMap F B)).ne_zero).mp hprime).irreducible
  let : IsPurelyInseparable B D := isPurelyInseparable_of_completedTensorEquiv F E B D η
  exact milnorKNorm_baseChange_of_prime_of_isPurelyInseparable_of_irreducible_map
    hp a ha hirr hdegree n x

section Branch

open _root_.AdicCompletion

variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [IsPurelyInseparable F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "CR" => AdicCompletion (maximalIdeal R) R
local notation "QR" => FractionRing CR
local notation "C" => fun q : IdealBranch J => FractionRing (BranchCompletion J q)

include F E in
/-- A purely inseparable fraction extension has at most one actual branch. -/
theorem subsingleton_idealBranch_of_isPurelyInseparable :
    Subsingleton (IdealBranch J) := by
  have hm : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  let e := Localization.primesOverEquivIdealBranch (T := S) (maximalIdeal R) hm
  let : Subsingleton ((maximalIdeal R).primesOver S) :=
    subsingleton_primesOver_of_isPurelyInseparable R S F E (maximalIdeal R)
  exact ⟨fun q q' => e.symm.injective (Subsingleton.elim _ _)⟩

/-- The actual fraction tensor decomposition evaluated at its sole branch. -/
def fractionTensorEquivPurelyInseparableBranch (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun r => localCompletionBaseAlgebra (S := S) (maximalIdeal R) r
    letI := fun r => localCompletionFractionAlgebra R S r
    QR ⊗[F] E ≃ₐ[QR] C q := by
  let := fractionCompletionAlgebra R F
  let := fun r => localCompletionBaseAlgebra (S := S) (maximalIdeal R) r
  let := fun r => localCompletionFractionAlgebra R S r
  let : Subsingleton (IdealBranch J) := subsingleton_idealBranch_of_isPurelyInseparable R S F E
  let g := Pi.evalAlgHom QR C q
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro a b h
      funext r
      obtain rfl : r = q := Subsingleton.elim _ _
      exact h
    · intro a
      exact ⟨fun r => (Subsingleton.elim q r) ▸ a, rfl⟩
  exact (fractionTensorEquivLocalFractionFields R S F E).trans (AlgEquiv.ofBijective g hg)

/-- On original upper elements the sole coordinate is the native completion fraction lift. -/
theorem fractionTensorEquivPurelyInseparableBranch_coordinate (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun r => localCompletionBaseAlgebra (S := S) (maximalIdeal R) r
    letI := fun r => localCompletionFractionAlgebra R S r
    letI := originalBranchFractionAlgebra S E q
    letI := originalBranchIsFractionRing S E q
    ((fractionTensorEquivPurelyInseparableBranch R S F E q).toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[F] QR ⊗[F] E).toRingHom) =
        IsFractionRing.lift (K := E)
          (fraction_algebraMap_injective (Localization.AtPrime q.val)) := by
  exact fractionTensorEquivLocalFractionFields_coordinate R S F E q

end Branch

end Stacks.Chow

end
