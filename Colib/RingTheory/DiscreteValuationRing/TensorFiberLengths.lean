/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.DVRResidueArbitrary
public import Colib.RingTheory.Charpoly.IntegralTensorProduct
public import Colib.RingTheory.DiscreteValuationRing.RamificationSquare
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.ResidueFieldTensor
public import Colib.RingTheory.Polynomial.PowerFactorCount
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Lengths of residue factors of a DVR tensor product

The multiplication characteristic polynomial on a finite residue tensor
product records its local lengths. A generator of the separable closure
distinguishes the actual maximal ideals, even when the residue extension
itself is not simple.
-/

@[expose] public noncomputable section

open Algebra IsLocalRing Polynomial
open scoped TensorProduct

universe u

namespace IsDiscreteValuationRing

/-- The field structure on the quotient at a maximal ideal. -/
local instance tensorFiberQuotientField {A : Type u} [CommRing A]
    (q : MaximalSpectrum A) : Field (A ⧸ q.asIdeal) :=
  Ideal.Quotient.field q.asIdeal

private theorem charpoly_lmul_eq_prod_residue_charpoly
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    [Fintype (MaximalSpectrum A)] (x : A) :
    (lmul K A x).charpoly = ∏ q : MaximalSpectrum A,
      (lmul K (A ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x)).charpoly ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let Aₚ (q : MaximalSpectrum A) := Localization.AtPrime q.asIdeal
  let : ∀ q, Module.Finite K (Aₚ q) := fun q =>
    Module.Finite.of_surjective (IsScalarTower.toAlgHom K A (Aₚ q)).toLinearMap
      (IsArtinianRing.localization_surjective q.asIdeal.primeCompl (Aₚ q))
  let ε : A ≃ₐ[K] (∀ q, Aₚ q) := (MaximalSpectrum.toPiLocalizationEquiv A).restrictScalars K
  rw [← Algebra.charpoly_lmul_algEquiv ε, Algebra.charpoly_lmul_pi]
  apply Finset.prod_congr rfl
  intro q _
  let η : (A ⧸ q.asIdeal) ≃ₐ[K] ResidueField (Aₚ q) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      q.asIdeal.bijective_algebraMap_quotient_residueField
  have hη : η (Ideal.Quotient.mk q.asIdeal x) = residue (Aₚ q) (ε x q) := rfl
  rw [Algebra.charpoly_lmul_eq_residue_charpoly_pow_length, ← hη,
    Algebra.charpoly_lmul_algEquiv η]

private theorem tensor_scalar_factor_minpoly_injective
    {k L M E : Type u} [Field k] [Field L] [Field M] [Field E]
    [Algebra k L] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    [IsPurelyInseparable M E] (pb : PowerBasis k M) :
    Function.Injective fun q : MaximalSpectrum (L ⊗[k] E) =>
      minpoly L (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k] algebraMap M E pb.gen)) := by
  classical
  let f : L ⊗[k] M →ₐ[L] L ⊗[k] E :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k M E)
  let g : M ⊗[k] L →ₐ[k] E ⊗[k] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k M E) (AlgHom.id k L)
  have hmap : f.toRingHom =
      ((Algebra.TensorProduct.comm k E L).toRingHom.comp g.toRingHom).comp
        (Algebra.TensorProduct.comm k L M).toRingHom := by
    have ha : f.restrictScalars k =
        ((Algebra.TensorProduct.comm k E L).toAlgHom.comp g).comp
          (Algebra.TensorProduct.comm k L M).toAlgHom := by
      ext <;> simp [f, g]
    exact congrArg (fun h : (L ⊗[k] M) →ₐ[k] L ⊗[k] E => h.toRingHom) ha
  have hinj : Function.Injective (PrimeSpectrum.comap f.toRingHom) := by
    have hg : Function.Injective (PrimeSpectrum.comap g.toRingHom) :=
      (PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
        (R := k) (K := M) (S := L) E).injective
    have h₁ : Function.Injective (PrimeSpectrum.comap
        (Algebra.TensorProduct.comm k L M).toRingHom) :=
      (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (Algebra.TensorProduct.comm k L M).bijective).injective
    have h₂ : Function.Injective (PrimeSpectrum.comap
        (Algebra.TensorProduct.comm k E L).toRingHom) :=
      (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (Algebra.TensorProduct.comm k E L).bijective).injective
    simpa only [hmap, PrimeSpectrum.comap_comp] using h₁.comp (hg.comp h₂)
  let r : L ⊗[k] M := 1 ⊗ₜ[k] pb.gen
  have hgen : Algebra.adjoin L {r} = ⊤ := by
    simpa only [Set.image_singleton] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := L) {pb.gen} pb.adjoin_gen_eq_top
  let : Module.Finite k M := pb.finite
  let pbt := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite L r) hgen
  intro q q' hqq'
  change minpoly L (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k] algebraMap M E pb.gen)) =
    minpoly L (Ideal.Quotient.mk q'.asIdeal (1 ⊗ₜ[k] algebraMap M E pb.gen)) at hqq'
  have hcomap : PrimeSpectrum.comap f.toRingHom q.toPrimeSpectrum =
      PrimeSpectrum.comap f.toRingHom q'.toPrimeSpectrum := by
    apply PrimeSpectrum.ext
    ext y
    obtain ⟨P, rfl⟩ := pbt.exists_eq_aeval' y
    let φ (q : MaximalSpectrum (L ⊗[k] E)) := (Ideal.Quotient.mkₐ L q.asIdeal).comp f
    have hφ (q : MaximalSpectrum (L ⊗[k] E)) :
        φ q pbt.gen = Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k] algebraMap M E pb.gen) := by
      rw [PowerBasis.ofAdjoinEqTop_gen]
      simp [φ, f, r]
    change f (aeval pbt.gen P) ∈ q.asIdeal ↔ f (aeval pbt.gen P) ∈ q'.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    change φ q (aeval pbt.gen P) = 0 ↔ φ q' (aeval pbt.gen P) = 0
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, ← minpoly.dvd_iff, ← minpoly.dvd_iff,
      hφ, hφ, hqq']
  exact MaximalSpectrum.ext (congrArg (fun z : PrimeSpectrum (L ⊗[k] E) => z.asIdeal)
    (hinj hcomap))

private theorem relative_adjoin_finrank_mul {K V W : Type u} [Field K] [Field V] [Field W]
    [Algebra K V] [Algebra K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₐ[K] W) (x : V) :
    let _ := f.toRingHom.toAlgebra
    Module.finrank (IntermediateField.adjoin K {f x}) W =
      Module.finrank V W * Module.finrank (IntermediateField.adjoin K {x}) V := by
  let : Algebra V W := f.toRingHom.toAlgebra
  have : IsScalarTower K V W := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let P := IntermediateField.adjoin K {x}
  let Q := IntermediateField.adjoin K {f x}
  have heq : Module.finrank K P = Module.finrank K Q := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite K x),
      IntermediateField.adjoin.finrank (IsIntegral.of_finite K (f x)),
      minpoly.algHom_eq f f.injective]
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := Q))
  calc
    _ = Module.finrank K W := Module.finrank_mul_finrank K Q W
    _ = Module.finrank K V * Module.finrank V W := (Module.finrank_mul_finrank K V W).symm
    _ = _ := by
      rw [← Module.finrank_mul_finrank K P V, heq]
      ring

section ArtinianFiber

variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A] [IsArtinianRing A]
  [Field V] [Algebra K V]

/-- The point at which a field receives an algebra map from an Artinian algebra. -/
def artinianFiberPoint (f : A →ₐ[K] V) : MaximalSpectrum A :=
  ⟨RingHom.ker f.toRingHom, (IsArtinianRing.isPrime_iff_isMaximal _).mp
    (RingHom.ker_isPrime f.toRingHom)⟩

/-- The induced algebra map from the actual residue quotient at the point. -/
def artinianFiberEmbedding (f : A →ₐ[K] V) :
    (A ⧸ (artinianFiberPoint f).asIdeal) →ₐ[K] V :=
  Ideal.Quotient.liftₐ (artinianFiberPoint f).asIdeal f fun _ hx => hx

/-- The induced residue map agrees with the original map on each class. -/
theorem artinianFiberEmbedding_mk (f : A →ₐ[K] V) (x : A) :
    artinianFiberEmbedding f (Ideal.Quotient.mk _ x) = f x := rfl

/-- The degree over the actual residue quotient, with its induced algebra structure. -/
def artinianFiberDegree (f : A →ₐ[K] V) : ℕ :=
  let _ := (artinianFiberEmbedding f).toRingHom.toAlgebra
  Module.finrank (A ⧸ (artinianFiberPoint f).asIdeal) V

end ArtinianFiber

open Classical in
private theorem artinian_fiber_weights_of_charpoly
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    [IsArtinianRing A]
    {ι : Type u} [Fintype ι] {V : ι → Type u} [∀ i, Field (V i)] [∀ i, Algebra K (V i)]
    [∀ i, FiniteDimensional K (V i)] (f : ∀ i, A →ₐ[K] V i)
    (x : A) (hsep : Function.Injective fun q : MaximalSpectrum A =>
      minpoly K (Ideal.Quotient.mk q.asIdeal x))
    (e : ℕ) (c : ι → ℕ)
    (hchar : (lmul K A x).charpoly ^ e = ∏ i, (lmul K (V i) (f i x)).charpoly ^ c i)
    (q : MaximalSpectrum A) :
    e * (Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).toNat =
      ∑ i, if artinianFiberPoint (f i) = q then c i * artinianFiberDegree (f i) else 0 := by
  classical
  let _ := Fintype.ofFinite (MaximalSpectrum A)
  let a (z : MaximalSpectrum A) := Ideal.Quotient.mk z.asIdeal x
  let P (z : MaximalSpectrum A) := minpoly K (a z)
  let Q (i : ι) := minpoly K (f i x)
  let m (z : MaximalSpectrum A) := (Module.length (Localization.AtPrime z.asIdeal)
    (Localization.AtPrime z.asIdeal)).toNat
  let d (z : MaximalSpectrum A) :=
    Module.finrank (IntermediateField.adjoin K {a z}) (A ⧸ z.asIdeal)
  let d' (i : ι) := Module.finrank (IntermediateField.adjoin K {f i x}) (V i)
  let z (i : ι) := artinianFiberPoint (f i)
  have hQ (i : ι) : Q i = P (z i) := by
    change minpoly K (f i x) = minpoly K (a (z i))
    rw [← artinianFiberEmbedding_mk (f i) x,
      minpoly.algHom_eq (artinianFiberEmbedding (f i)) (artinianFiberEmbedding (f i)).injective]
  have hd (i : ι) : d' i = artinianFiberDegree (f i) * d (z i) := by
    change Module.finrank (IntermediateField.adjoin K {f i x}) (V i) = _
    rw [← artinianFiberEmbedding_mk (f i) x]
    exact relative_adjoin_finrank_mul (artinianFiberEmbedding (f i)) (a (z i))
  have hprod : (∏ z, P z ^ (e * m z * d z)) = ∏ i, Q i ^ (c i * d' i) := by
    calc
      _ = (∏ z : MaximalSpectrum A,
          (lmul K (A ⧸ z.asIdeal) (a z)).charpoly ^ m z) ^ e := by
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro z _
        rw [Algebra.charpoly_lmul_eq_minpoly_pow_arbitrary, ← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = (lmul K A x).charpoly ^ e := by rw [charpoly_lmul_eq_prod_residue_charpoly]
      _ = _ := hchar
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Algebra.charpoly_lmul_eq_minpoly_pow_arbitrary, ← pow_mul, Nat.mul_comm]
  have hP (z : MaximalSpectrum A) : (P z).Monic ∧ Irreducible (P z) :=
    ⟨minpoly.monic (IsIntegral.of_finite K (a z)),
      minpoly.irreducible (IsIntegral.of_finite K (a z))⟩
  have hQ' (i : ι) : (Q i).Monic ∧ Irreducible (Q i) := by
    rw [hQ i]
    exact hP (z i)
  have hcount := congrArg (fun p : K[X] => (UniqueFactorizationMonoid.normalizedFactors p).count
    (P q)) hprod
  rw [Polynomial.count_normalizedFactors_prod_irreducible_pow _ _ hP,
    Polynomial.count_normalizedFactors_prod_irreducible_pow _ _ hQ'] at hcount
  have hP_eq (q' : MaximalSpectrum A) : P q' = P q ↔ q' = q := hsep.eq_iff
  simp_rw [hQ, hP_eq, hd] at hcount
  have hright :
      (∑ i, if z i = q then c i * (artinianFiberDegree (f i) * d (z i)) else 0) =
        (∑ i, if z i = q then c i * artinianFiberDegree (f i) else 0) * d q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · rw [h, Nat.mul_assoc]
    · rw [Nat.zero_mul]
  rw [hright] at hcount
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := IntermediateField.adjoin K {a q})
    (M := A ⧸ q.asIdeal))
  simpa [m, z] using hcount

section ResidueTensor

variable (R S T U : Type u)
  [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]
  [CommRing U] [IsLocalRing U] [Algebra R S] [Algebra R T] [Algebra R U]
  [Algebra S U] [Algebra T U] [IsScalarTower R S U] [IsScalarTower R T U]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
  [IsLocalHom (algebraMap R U)] [IsLocalHom (algebraMap S U)] [IsLocalHom (algebraMap T U)]

-- The tensor of the actual residue maps is re-exported from the canonical Stacks module.

/-- The source residue field maps through the original upper local ring map. -/
theorem residueTensorMap_one_tmul (s : ResidueField S) :
    residueTensorMap R S T U (1 ⊗ₜ[ResidueField R] s) =
      ResidueField.map (algebraMap S U) s := by
  simp only [residueTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end ResidueTensor

section DVR

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

open Classical in
/-- The length at each actual residue tensor point, times the original
ramification index, is the ramification-weighted sum of residue degrees above it. -/
theorem residueTensorLength_mul_ramification_eq_sum
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i))
    (hcoords : ∀ i (s : S), algebraMap (U i) (D i) (algebraMap S (U i) s) =
      ε (1 ⊗ₜ[F] (algebraMap S E s)) i)
    {π : R} {ϖ : S} {τ : T} (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (ρ : ∀ i, U i) (hρ : ∀ i, Irreducible (ρ i)) (z : ∀ i, (U i)ˣ) (c : ι → ℕ)
    (hc : ∀ i, algebraMap T (U i) τ = (z i : U i) * ρ i ^ c i)
    (q : MaximalSpectrum (ResidueField T ⊗[ResidueField R] ResidueField S)) :
    let _ : IsArtinianRing (ResidueField T ⊗[ResidueField R] ResidueField S) :=
      IsArtinianRing.of_finite (ResidueField T) _
    e * (Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).toNat =
      ∑ i, if artinianFiberPoint (residueTensorMap R S T (U i)) = q then
        c i * artinianFiberDegree (residueTensorMap R S T (U i)) else 0 := by
  classical
  let k := ResidueField R
  let K := ResidueField T
  let H := ResidueField S
  let A := K ⊗[k] H
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let _ := Fintype.ofFinite (MaximalSpectrum A)
  let M := separableClosure k H
  let pb := Field.powerBasisOfFiniteOfSeparable k M
  obtain ⟨θ, hθ⟩ := residue_surjective (R := S) (algebraMap M H pb.gen)
  let x : A := 1 ⊗ₜ[k] residue S θ
  let f (i : ι) := residueTensorMap R S T (U i)
  have hf (i : ι) : f i x = residue (U i) (algebraMap S (U i) θ) := by
    change residueTensorMap R S T (U i) (1 ⊗ₜ[k] residue S θ) = _
    rw [residueTensorMap_one_tmul, ResidueField.map_residue]
  have hsep : Function.Injective fun q : MaximalSpectrum A =>
      minpoly K (Ideal.Quotient.mk q.asIdeal x) := by
    dsimp only [x]
    rw [hθ]
    exact tensor_scalar_factor_minpoly_injective pb
  have hchar : (lmul K A x).charpoly ^ e =
      ∏ i, (lmul K (ResidueField (U i)) (f i x)).charpoly ^ c i := calc
    _ = (((lmul R S θ).charpoly.map (residue R)).map (algebraMap k K)) := by
      rw [Algebra.residue_charpoly_lmul_eq_pow_arbitrary R S hπ hϖ u e he θ,
        Polynomial.map_pow, ← LinearMap.charpoly_baseChange, Algebra.baseChange_lmul]
    _ = ((lmul R S θ).charpoly.map (algebraMap R T)).map (residue T) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    _ = _ := by
      rw [Algebra.map_charpoly_lmul_eq_prod_integralClosure R F S E T L D U ε θ
        (fun i => algebraMap S (U i) θ) (fun i => hcoords i θ), Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [hf, Algebra.residue_charpoly_lmul_eq_pow_arbitrary T (U i) hτ (hρ i)
        (z i) (c i) (hc i)]
  exact artinian_fiber_weights_of_charpoly f x hsep e c hchar q

end DVR

end IsDiscreteValuationRing

end
