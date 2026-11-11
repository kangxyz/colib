/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.TensorFiberLengths
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTensorBaseChangeFinite
public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

/-!
# Ramification-weighted residue norm base change for finite extensions

The local lengths of the original residue tensor product supply the
multiplicities in the finite norm base-change formula. The ramification
square then converts the upper lengths to the weights of the original
residue restrictions.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing IsDiscreteValuationRing
open scoped TensorProduct

attribute [local instance] Ideal.Quotient.field

universe u

private theorem ramification_fiber_weights {ι J : Type u} [Fintype ι] [DecidableEq J]
    (q : ι → J) (r : J) (e a m : ℕ) (b c d : ι → ℕ)
    (he : 0 < e) (hsquare : ∀ i, e * b i = a * c i)
    (hfiber : e * m = ∑ i, if q i = r then c i * d i else 0) :
    (∑ i, if q i = r then b i * d i else 0) = a * m := by
  apply Nat.eq_of_mul_eq_mul_left he
  calc
    _ = ∑ i, if q i = r then (e * b i) * d i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [Nat.mul_assoc, Nat.mul_zero]
    _ = ∑ i, if q i = r then (a * c i) * d i else 0 := by simp_rw [hsquare]
    _ = a * ∑ i, if q i = r then c i * d i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [Nat.mul_assoc, Nat.mul_zero]
    _ = _ := by rw [← hfiber]; ring

private theorem finite_norm_through_residue_tower {K Z W : Type u}
    [Field K] [Field Z] [Field W] [Algebra K Z] [Algebra K W] [Algebra Z W]
    [IsScalarTower K Z W] [FiniteDimensional K Z] [FiniteDimensional K W]
    [FiniteDimensional Z W] (n : ℕ) (y : MilnorKTheory Z n) :
    milnorKNorm K W n (milnorKTransport (algebraMap Z W) n y) =
      Module.finrank Z W • milnorKNorm K Z n y := by
  have h := milnorKNorm_milnorKTransport Z W n y
  rw [natCast_zsmul] at h
  calc
    _ = milnorKNorm K Z n (milnorKNorm Z W n (milnorKTransport (algebraMap Z W) n y)) :=
      (milnorKNorm_tower_of_finite (M := Z) n _).symm
    _ = _ := (congrArg (milnorKNorm K Z n) h).trans (map_nsmul _ _ _)

private theorem sum_fiber_norm_weights {ι J M : Type u} [Fintype ι] [Fintype J]
    [DecidableEq J] [AddCommMonoid M] (q : ι → J) (b d : ι → ℕ) (w : J → ℕ) (t : J → M)
    (h : ∀ r, (∑ i, if q i = r then b i * d i else 0) = w r) :
    (∑ r, w r • t r) = ∑ i, b i • (d i • t (q i)) := by
  calc
    _ = ∑ r, (∑ i, if q i = r then b i * d i else 0) • t r := by simp_rw [h]
    _ = ∑ i, (b i * d i) • t (q i) := by
      simp_rw [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (q i)]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · simp
    _ = _ := by simp only [mul_smul]

variable (R F S E T L : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type u} [Fintype ι] (D U : ι → Type u)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Algebra S (U i)] [∀ i, Algebra R (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap R (U i))]

/-- Weighted base change for the actual residue norms along the full generic
tensor decomposition. The residue fields may be inseparable. -/
theorem milnorKNorm_residue_weighted_baseChange_of_finite
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i))
    (hcoords : ∀ i (s : S), algebraMap (U i) (D i) (algebraMap S (U i) s) =
      ε (1 ⊗ₜ[F] (algebraMap S E s)) i)
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (ρ : ∀ i, U i) (hρ : ∀ i, Irreducible (ρ i))
    (w z : ∀ i, (U i)ˣ) (b c : ι → ℕ)
    (hb : ∀ i, algebraMap S (U i) ϖ = (w i : U i) * ρ i ^ b i)
    (hc : ∀ i, algebraMap T (U i) τ = (z i : U i) * ρ i ^ c i)
    (n : ℕ) (x : MilnorKTheory (ResidueField S) n) :
    a • milnorKTransport (algebraMap (ResidueField R) (ResidueField T)) n
      (milnorKNorm (ResidueField R) (ResidueField S) n x) =
      ∑ i, b i • milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTransport (ResidueField.map (algebraMap S (U i))) n x) := by
  classical
  let k := ResidueField R
  let K := ResidueField T
  let H := ResidueField S
  let A := K ⊗[k] H
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let _ := Fintype.ofFinite (MaximalSpectrum A)
  let f (i : ι) := residueTensorMap R S T (U i)
  let q (i : ι) := artinianFiberPoint (f i)
  let d (i : ι) := artinianFiberDegree (f i)
  have hepos : 0 < e := by
    by_contra h
    have hz : e = 0 := Nat.eq_zero_of_not_pos h
    apply hπ.not_isUnit
    apply IsUnit.of_map (algebraMap R S) π
    rw [he, hz, pow_zero, mul_one]
    exact u.isUnit
  have hsquare (i : ι) : e * b i = a * c i := by
    apply IsDiscreteValuationRing.ramification_square_of_uniformizer_equations (U := U i)
      (algebraMap R S) (algebraMap R T) (algebraMap S (U i)) (algebraMap T (U i))
      _ (hρ i) u v (w i) (z i) e a (b i) (c i) he ha (hb i) (hc i)
    ext r
    exact (IsScalarTower.algebraMap_apply R S (U i) r).symm.trans
      (IsScalarTower.algebraMap_apply R T (U i) r)
  have hweight (r : MaximalSpectrum A) :
      (∑ i, if q i = r then b i * d i else 0) = a * tensorNormFactorLength r := by
    have hfiber : e * tensorNormFactorLength r =
        ∑ i, if q i = r then c i * d i else 0 :=
      residueTensorLength_mul_ramification_eq_sum R F S E T L D U ε hcoords hπ hϖ hτ
        u e he ρ hρ z c hc r
    exact ramification_fiber_weights q r e a (tensorNormFactorLength r) b c d hepos hsquare hfiber
  let t (r : MaximalSpectrum A) : MilnorKTheory K n :=
    milnorKNorm K (A ⧸ r.asIdeal) n (milnorKTransport (tensorNormFactorMap r) n x)
  have hterm (i : ι) :
      milnorKNorm K (ResidueField (U i)) n
          (milnorKTransport (ResidueField.map (algebraMap S (U i))) n x) =
        d i • t (q i) := by
    let Z := A ⧸ (q i).asIdeal
    let W := ResidueField (U i)
    let g : Z →ₐ[K] W := artinianFiberEmbedding (f i)
    let : Algebra Z W := g.toRingHom.toAlgebra
    have : IsScalarTower K Z W := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    let : FiniteDimensional Z W := FiniteDimensional.right K Z W
    have hcomp : (algebraMap Z W).comp (tensorNormFactorMap (q i)) =
        ResidueField.map (algebraMap S (U i)) := by
      ext s
      change artinianFiberEmbedding (f i) (Ideal.Quotient.mk _ (1 ⊗ₜ[k] s)) =
        ResidueField.map (algebraMap S (U i)) s
      rw [artinianFiberEmbedding_mk, residueTensorMap_one_tmul]
    have hx : milnorKTransport (ResidueField.map (algebraMap S (U i))) n x =
        milnorKTransport (algebraMap Z W) n (milnorKTransport (tensorNormFactorMap (q i)) n x) := by
      rw [milnorKTransport_comp_apply, hcomp]
    calc
      _ = milnorKNorm K W n
          (milnorKTransport (algebraMap Z W) n
            (milnorKTransport (tensorNormFactorMap (q i)) n x)) :=
        congrArg (milnorKNorm K W n) hx
      _ = _ := finite_norm_through_residue_tower n
        (milnorKTransport (tensorNormFactorMap (q i)) n x)
  have hbase : milnorKTransport (algebraMap k K) n (milnorKNorm k H n x) =
      ∑ r : MaximalSpectrum A, tensorNormFactorLength r • t r := by
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
      natCast_zsmul] using
      milnorKNorm_map_eq_weighted_sum_tensorFactors_of_finite (k := k) (L := K) (E := H) n x
  calc
    _ = a • ∑ r : MaximalSpectrum A, tensorNormFactorLength r • t r :=
      congrArg (fun y : MilnorKTheory K n => a • y) hbase
    _ = ∑ r : MaximalSpectrum A, (a * tensorNormFactorLength r) • t r := by
      rw [Finset.smul_sum]
      simp only [mul_smul]
    _ = ∑ i, b i • (d i • t (q i)) :=
      sum_fiber_norm_weights q b d (fun r => a * tensorNormFactorLength r) t hweight
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun y : MilnorKTheory K n => b i • y) (hterm i).symm

end Stacks.Chow

end
