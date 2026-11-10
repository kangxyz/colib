/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTensorBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChangeSeparable

/-!
# Separable normal-prime norms under an actual full tensor decomposition

Separability is required only for the source extension. The coefficient extension
is arbitrary. Actual coordinate power bases supply the complete family of literal
polynomial factors, their quotient equivalences and the original coefficient maps.
The scalar formula gives the unweighted sum of the existing chosen factor norms.

Normality and separability of actual branches are conclusions. Finite dimensionality
comes from native power bases, with no branch norm, comparison or norm-square premise.
All product indices and every homogeneous degree, including zero, are retained.
-/

@[expose] public noncomputable section

open Polynomial Module
open scoped TensorProduct

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Normal F E]
  {ι : Type v} [Fintype ι] {D : ι → Type u}
  [∀ j, Field (D j)] [∀ j, Algebra K (D j)]

omit [FiniteDimensional F E] [Normal F E] [Fintype ι] in
/-- Every actual tensor field factor of a simple separable extension is separable.
No separability, perfectness or algebraicity of the coefficient extension is assumed. -/
theorem isSeparable_of_tensorProductPiEquiv [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (j : ι) :
    Algebra.IsSeparable K (D j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := pb.exists_powerBasis_of_tensorProductPiEquiv ε j
  have hint : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) := hb ▸ b.isIntegral_gen
  let q : MonicIrreducibleOfDegree K (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree :=
    minpolyOfDegree K hint
  have hsep : (minpoly F pb.gen).Separable := Algebra.IsSeparable.isSeparable F pb.gen
  have hqsep : (poly q).Separable :=
    (hsep.map (f := algebraMap F K)).of_dvd (pb.minpoly_tensorProductPiEquiv_gen_dvd ε j)
  obtain ⟨_g, e, _hg, _he, _hcoordinate⟩ :=
    pb.exists_adjoinRoot_equiv_tensorProductPiEquiv_map ε
  let e₀ : (K[X] ⧸ Ideal.span {poly q}) ≃ₐ[K] D j :=
    { toRingEquiv := (e j).toRingEquiv
      commutes' := (e j).commutes }
  let : Algebra.IsSeparable K (K[X] ⧸ Ideal.span {poly q}) :=
    isSeparable_quotient_of_polynomial_separable q hqsep
  exact AlgEquiv.Algebra.isSeparable e₀

omit [FiniteDimensional F E] [Fintype ι] in
/-- The actual degree of each tensor-product field factor is one or the original prime
degree. This supplies the degree alternative needed by the completed-branch mixed theorem. -/
theorem finrank_eq_one_or_eq_of_tensorProductPiEquiv_of_normal_prime_of_separable [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (j : ι) :
    finrank K (D j) = 1 ∨ finrank K (D j) = finrank F E := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := pb.exists_powerBasis_of_tensorProductPiEquiv ε j
  have hint : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) := hb ▸ b.isIntegral_gen
  let p : MonicIrreducibleOfDegree F (minpoly F pb.gen).natDegree :=
    minpolyOfDegree F pb.isIntegral_gen
  let q : MonicIrreducibleOfDegree K (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree :=
    minpolyOfDegree K hint
  have hsource : (minpoly F pb.gen).natDegree = finrank F E :=
    pb.natDegree_minpoly.trans pb.finrank.symm
  have htarget : (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree = finrank K (D j) := by
    rw [← hb]
    exact b.natDegree_minpoly.trans b.finrank.symm
  have hp' : Nat.Prime (minpoly F pb.gen).natDegree := hsource.symm ▸ hp
  obtain ⟨g, _e, _hg, _he, _hcoordinate⟩ :=
    pb.exists_adjoinRoot_equiv_tensorProductPiEquiv_map ε
  let g₀ : (F[X] ⧸ Ideal.span {poly p}) ≃ₐ[F] E :=
    { toRingEquiv := g.toRingEquiv
      commutes' := g.commutes }
  let : Normal F (F[X] ⧸ Ideal.span {poly p}) := Normal.of_algEquiv g₀.symm
  have h := degree_eq_one_or_eq_of_dvd_map_of_normal_prime_of_separable
    (algebraMap F K) p (Algebra.IsSeparable.isSeparable F pb.gen) hp' q
    (pb.minpoly_tensorProductPiEquiv_gen_dvd ε j)
  simpa only [htarget, hsource] using h

/-- The actual chosen norm commutes with arbitrary scalar extension followed by the
full specified tensor decomposition. Every actual factor occurs once. -/
theorem milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (x : MilnorKRing E) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) := by
  classical
  let b (j : ι) : PowerBasis K (D j) :=
    Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)
  have hb (j : ι) : (b j).gen = ε (1 ⊗ₜ[F] pb.gen) j :=
    Classical.choose_spec (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)
  let : ∀ j, FiniteDimensional K (D j) := fun j => (b j).finite
  change milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) = _
  have hint (j : ι) : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) :=
    hb j ▸ (b j).isIntegral_gen
  let p : MonicIrreducibleOfDegree F (minpoly F pb.gen).natDegree :=
    minpolyOfDegree F pb.isIntegral_gen
  let q (j : ι) : MonicIrreducibleOfDegree K
      (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree := minpolyOfDegree K (hint j)
  have hp' : Nat.Prime (minpoly F pb.gen).natDegree := by
    rw [pb.natDegree_minpoly, ← pb.finrank]
    exact hp
  have hsep : (minpoly F pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable F pb.gen
  have hq (j : ι) : poly (q j) ∣ (poly p).map (algebraMap F K) :=
    pb.minpoly_tensorProductPiEquiv_gen_dvd ε j
  have hinj : Set.InjOn (fun j => poly (q j)) ((Finset.univ : Finset ι) : Set ι) := by
    intro i _ j _ hij
    exact pb.minpoly_tensorProductPiEquiv_gen_injective ε hsep hij
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map (algebraMap F K) →
        ∃ j ∈ (Finset.univ : Finset ι), poly r = poly (q j) := by
    intro a r hr
    have hnonzero : (poly p).map (algebraMap F K) ≠ 0 := ((monic p).map _).ne_zero
    have hrmem := (Polynomial.mem_normalizedFactors_iff hnonzero).mpr
      ⟨irreducible r, monic r, hr⟩
    obtain ⟨j, hj⟩ :=
      (pb.mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv ε (poly r)).mp hrmem
    exact ⟨j, Finset.mem_univ j, hj.symm⟩
  obtain ⟨g, e, _hg, _he, hcoordinate⟩ :=
    pb.exists_adjoinRoot_equiv_tensorProductPiEquiv_map ε
  -- Fix the native quotient field instances before forming any Milnor maps.
  let g₀ : (F[X] ⧸ Ideal.span {poly p}) ≃ₐ[F] E :=
    { toRingEquiv := g.toRingEquiv
      commutes' := g.commutes }
  let e₀ (j : ι) : (K[X] ⧸ Ideal.span {poly (q j)}) ≃ₐ[K] D j :=
    { toRingEquiv := (e j).toRingEquiv
      commutes' := (e j).commutes }
  let m (j : ι) : (F[X] ⧸ Ideal.span {poly p}) →+*
      (K[X] ⧸ Ideal.span {poly (q j)}) :=
    AdjoinRoot.map (algebraMap F K) (poly p) (poly (q j)) (hq j)
  let jmap (j : ι) : E →+* D j :=
    (Pi.evalRingHom D j).comp
      (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hforward (j : ι) : (e₀ j).toRingHom.comp (m j) =
      (jmap j).comp g₀.toRingHom := hcoordinate j
  have hsquare (j : ι) : (e₀ j).symm.toRingHom.comp (jmap j) =
      (m j).comp g₀.symm.toRingHom := by
    apply RingHom.ext
    intro a
    change (e₀ j).symm (jmap j a) = m j (g₀.symm a)
    apply (e₀ j).injective
    calc
      e₀ j ((e₀ j).symm (jmap j a)) = jmap j a := (e₀ j).apply_symm_apply _
      _ = jmap j (g₀ (g₀.symm a)) := by rw [g₀.apply_symm_apply]
      _ = e₀ j (m j (g₀.symm a)) := (RingHom.congr_fun (hforward j) _).symm
  exact milnorKNormRing_map_eq_sum_of_branch_equivs_of_normal_prime_of_separable
    (algebraMap F K) p hsep hp' g₀.symm (Finset.univ : Finset ι)
    (fun j => (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree) q hinj hq hcover D
    (fun j => (e₀ j).symm) jmap hsquare x

/-- The full tensor-product chosen-norm formula as an equality of native additive maps. -/
theorem milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKRingMap (algebraMap F K)).toAddMonoidHom.comp (milnorKNormRing F E) =
      ∑ j, (milnorKNormRing K (D j)).comp
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))).toAddMonoidHom := by
  classical
  let : ∀ j, FiniteDimensional K (D j) :=
    fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply]
  exact milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp x

/-- The full tensor-product norm formula in every homogeneous degree, including zero. -/
theorem milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E n) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTheoryMap (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTheoryMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) := by
  classical
  let : ∀ j, FiniteDimensional K (D j) :=
    fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
  change milnorKTheoryMap (algebraMap F K) n (milnorKNorm F E n x) = _
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  change milnorKRingMap (algebraMap F K) (milnorKNormRing F E (x : MilnorKRing E)) =
    (milnorKGrading K n).subtype (∑ j, milnorKNorm K (D j) n
      (milnorKTransport ((Pi.evalRingHom D j).comp
        (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x))
  rw [map_sum]
  exact milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp
    (x : MilnorKRing E)

end Stacks.Chow

end
