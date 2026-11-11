/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormPrimeInduction
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPresentationTransport
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionTower
public import Colib.FieldTheory.PGroupNormalSubfieldEmbedding
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable
public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

/-!
# The diagonal norm comparison in a Galois p-group ambient

An embedded field of composite degree has a normal prime-degree subfield.
Both degrees of the resulting tower are strictly smaller. The native chosen
Milnor norm and diagonal corestriction each compose through this tower.

Adapted from `Motivic/Cohomology/Diagonal/PolynomialNormPGroupInduction.lean:43-155`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormInduction

open DiagonalCorestriction DiagonalMilnorSymbol MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance pGroupRootIrreducible {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance pGroupRootFinite {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) :
    FiniteDimensional F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

local instance pGroupRootCharZero {F : Type u} [Field F] [CharZero F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : CharZero (AdjoinRoot (poly p)) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot (poly p))).injective

variable {k : Type u} [Field k] [CharZero k]

/-- Comparison on a literal polynomial quotient gives comparison on any
actual algebra-equivalent finite field. -/
theorem rawSymbol_milnorKNorm_of_presentation
    {E : Type u} [Field E] [CharZero E] [Algebra k E] [FiniteDimensional k E]
    (n : ℕ) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (ε : E ≃ₐ[k] AdjoinRoot (poly p))
    (h : ∀ y : MilnorKTheory (AdjoinRoot (poly p)) n,
      rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n y) =
        corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n y))
    (x : MilnorKTheory E n) :
    rawSymbol k n (milnorKNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) := by
  rw [← milnorKNorm_map_algEquiv_of_isSeparable ε n x, h]
  exact (corestriction_rawSymbol_algEquiv ε n x).symm

private theorem rawSymbol_milnorKNorm_of_lower_degrees
    {E : Type u} [Field E] [CharZero E] [Algebra k E] [FiniteDimensional k E]
    (n d : ℕ) (hd : Module.finrank k E < d)
    (ih : ∀ {e : ℕ} (p : MonicIrreducibleOfDegree k e), e < d →
      ∀ y : MilnorKTheory (AdjoinRoot (poly p)) n,
        rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n y) =
          corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n y))
    (x : MilnorKTheory E n) :
    rawSymbol k n (milnorKNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) := by
  obtain ⟨e, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k E
  have hdegree : Module.finrank k E = e :=
    ε.toLinearEquiv.finrank_eq.trans
      (finrank_quotient_span_eq_natDegree.trans (natDegree_eq p))
  have hp : e < d := by rwa [← hdegree]
  exact rawSymbol_milnorKNorm_of_presentation n p ε (ih p hp) x

private theorem rawSymbol_polynomialNorm_of_degree_one (n : ℕ)
    (p : MonicIrreducibleOfDegree k 1) (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) := by
  let E := AdjoinRoot (poly p)
  have hd : Module.finrank k E = 1 :=
    finrank_quotient_span_eq_natDegree.trans (natDegree_eq p)
  let ε : k ≃ₐ[k] E := AlgEquiv.ofBijective (Algebra.ofId k E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  let y := milnorKTheoryMap ε.symm.toRingHom n x
  have hcomp : (algebraMap k E).comp ε.symm.toRingHom = RingHom.id E := by
    apply RingHom.ext
    intro z
    exact ε.apply_symm_apply z
  have hy : milnorKTheoryMap (algebraMap k E) n y = x := by
    dsimp only [y]
    rw [← LinearMap.comp_apply, ← milnorKTheoryMap_comp, hcomp, milnorKTheoryMap_id,
      LinearMap.id_apply]
  have hnorm : milnorKNorm k E n x = y := by
    calc
      _ = milnorKNorm k E n (milnorKTransport (algebraMap k E) n y) :=
        congrArg (fun z => milnorKNorm k E n z) (by
          simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap]
            using hy.symm)
      _ = y := by
        rw [milnorKNorm_milnorKTransport k E, hd, Nat.cast_one, one_zsmul]
  rw [hnorm]
  simpa only [y, corestriction_id, AddMonoidHom.id_apply] using
    (corestriction_rawSymbol_algEquiv ε.symm n x).symm

/-- For a branch embedded in a finite Galois p-group extension, the comparison
follows from prime-degree comparison and strict lower-degree comparison over
every characteristic-zero field. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormPGroupInduction.lean:108-155"
  "adaptation" "Degree induction using the native separable norm and finite transfer towers"]
theorem rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees
    {Ω : Type u} [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
    (n d : ℕ) {e : ℕ} (p : MonicIrreducibleOfDegree k e) (hd : e ≤ d)
    (g : AdjoinRoot (poly p) →ₐ[k] Ω)
    (ih : ∀ (L : Type u) [Field L] [CharZero L] {a : ℕ}
      (r : MonicIrreducibleOfDegree L a), a < d → ∀ y : MilnorKTheory (AdjoinRoot (poly r)) n,
        rawSymbol L n (milnorKNorm L (AdjoinRoot (poly r)) n y) =
          corestriction (k := L) n (rawSymbol (AdjoinRoot (poly r)) n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) := by
  by_cases hpone : e = 1
  · subst e
    exact rawSymbol_polynomialNorm_of_degree_one n p x
  by_cases hpprime : e.Prime
  · apply rawSymbol_polynomialNorm_prime_of_lower_degrees (p := p) n hpprime ?_ x
    intro a r hr y
    exact ih (AdjoinRoot (poly p)) r (hr.trans_le hd) y
  let E := AdjoinRoot (poly p)
  have hdegree : Module.finrank k E = e :=
    finrank_quotient_span_eq_natDegree.trans (natDegree_eq p)
  have hdim : 1 < Module.finrank k E := by
    have hpos := (irreducible p).natDegree_pos
    rw [natDegree_eq p] at hpos
    omega
  obtain ⟨R, _, hrdegree, hupper⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hG g hdim
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap k R).injective
  let : FiniteDimensional R E := FiniteDimensional.right k R E
  have hE : Module.finrank k E ≤ d := by rwa [hdegree]
  have hlower : Module.finrank k R < d := by
    have hle : Module.finrank k R ≤ Module.finrank k E := by
      rw [← Module.finrank_mul_finrank k R E]
      exact Nat.le_mul_of_pos_right _ Module.finrank_pos
    have hne : Module.finrank k R ≠ Module.finrank k E := by
      intro heq
      apply hpprime
      rw [← hdegree, ← heq, hrdegree]
      exact Fact.out
    exact (lt_of_le_of_ne hle hne).trans_le hE
  have hupper' : Module.finrank R E < d := hupper.trans_le hE
  rw [← milnorKNorm_tower_of_isSeparable (M := R) n x,
    rawSymbol_milnorKNorm_of_lower_degrees n d hlower (ih k),
    rawSymbol_milnorKNorm_of_lower_degrees n d hupper' (ih R)]
  exact DFunLike.congr_fun (corestriction_comp (k := k) (L := R) (E := E) n)
    (rawSymbol E n x)

end AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormInduction
