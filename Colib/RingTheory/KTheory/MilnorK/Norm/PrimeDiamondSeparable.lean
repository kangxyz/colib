/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFiniteResidueSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeSingleLiftSeparable

/-!
# The native separable normal-prime norm diamond

A genuine native homogeneous single-residue lift computes the first iterated
simple norm as minus infinity of its chosen rational norm. The complete finite
residue formula contracts that lift to its original lower polynomial, with the
actual tensor-swap quotient map on its sole surviving residue. The original
`simpleMilnorNorm_eq` then closes the diamond. Additive generation extends the
result from every homogeneous degree to the entire native Milnor K-ring.

The proof route is adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/PrimeDiamond.lean`
at revision `52e09db47998f139064acf48a2d3a64494d0dd9a`. Its alternate polynomial norm,
residue, branch and Milnor K models are neither imported nor copied. All maps and
carriers below are the original Stacks and Mathlib objects. Only the original prime-degree
constant polynomial is required to be separable. The lower polynomial and all other
auxiliary closed points remain arbitrary. No tower law, residue square or norm comparison
is assumed.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

local instance primeDiamondSeparable_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance primeDiamondSeparable_rootFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance primeDiamondSeparable_rationalFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ}

section FiniteSupport

variable (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

/-- A literal upper native factor cannot also divide the coefficient image of
a distinct lower native polynomial. No characteristic or normality is needed. -/
private theorem primeDiamondSeparable_not_dvd_map_of_ne
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    {e' : ℕ} (h' : MonicIrreducibleOfDegree k e') (hne : poly h' ≠ poly h) :
    ¬poly q.1.2 ∣ (poly h').map (algebraMap k E) := by
  intro hq
  apply hne
  have hdiv : poly h ∣ poly h' :=
    (Polynomial.dvd_map_iff_of_dvd_irreducible_map (algebraMap k E)
      (irreducible h) (irreducible q.1.2).not_isUnit q.2 (poly h')).mp hq
  exact (Polynomial.eq_of_monic_of_associated (monic h) (monic h')
    ((irreducible h).associated_of_dvd (irreducible h') hdiv)).symm

/-- In the complete literal upper-factor sum, a single-residue lift leaves
exactly its actual tensor-matched quotient term. -/
private theorem primeDiamondSeparable_sum_eq_matched_of_singleLift
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) (x : MilnorKRing (RatFunc E))
    (hx : IsSingleResidueLift q.1.2 z x) :
    (∑ i ∈ S.attach,
      let q' : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
          poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
      let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q'
      simpleMilnorNorm r.1.2
        (@milnorKRingMap
          (E[X] ⧸ Ideal.span {poly q'.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
          (Ideal.Quotient.field _) (Ideal.Quotient.field _)
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q').toRingHom
          (monicIrreducibleResidue q'.1.2 x))) =
      simpleMilnorNorm
        (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
        (milnorKRingMap
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom z) := by
  classical
  let i₀ : S := ⟨q.1, (hS q.1).mpr q.2⟩
  rw [Finset.sum_eq_single i₀]
  · change simpleMilnorNorm
        (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
        (milnorKRingMap
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
          (monicIrreducibleResidue q.1.2 x)) = _
    rw [hx.1]
  · intro i _ hi
    have hne : poly i.1.2 ≠ poly q.1.2 := by
      intro heq
      apply hi
      apply Subtype.ext
      exact sigma_poly_injective heq
    let q' : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
        poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
    let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q'
    let F : (E[X] ⧸ Ideal.span {poly i.1.2}) →+*
        ((AdjoinRoot (poly h))[X] ⧸ Ideal.span {poly r.1.2}) :=
      (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q').toRingHom
    let g : MilnorKRing (E[X] ⧸ Ideal.span {poly i.1.2}) →+
        MilnorKRing (AdjoinRoot (poly h)) :=
      (simpleMilnorNorm r.1.2).comp (milnorKRingMap F).toAddMonoidHom
    change g (monicIrreducibleResidue i.1.2 x) = 0
    exact (congrArg g (hx.2 i.1.1 i.1.2 hne)).trans (map_zero g)
  · intro hnot
    exact (hnot (Finset.mem_attach S i₀)).elim

/-- Above every other lower native polynomial all terms of the complete factor
sum vanish. The exclusion is proved from actual coefficient divisibility. -/
private theorem primeDiamondSeparable_sum_eq_zero_of_singleLift
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    {e' : ℕ} (h' : MonicIrreducibleOfDegree k e') (hne : poly h' ≠ poly h)
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h').map (algebraMap k E))
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) (x : MilnorKRing (RatFunc E))
    (hx : IsSingleResidueLift q.1.2 z x) :
    (∑ i ∈ S.attach,
      let q' : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
          poly q.2 ∣ (poly h').map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
      let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h') q'
      simpleMilnorNorm r.1.2
        (@milnorKRingMap
          (E[X] ⧸ Ideal.span {poly q'.1.2}) ((AdjoinRoot (poly h'))[X] ⧸ Ideal.span {poly r.1.2})
          (Ideal.Quotient.field _) (Ideal.Quotient.field _)
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h') q').toRingHom
          (monicIrreducibleResidue q'.1.2 x))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  have hne' : poly i.1.2 ≠ poly q.1.2 := by
    intro heq
    apply primeDiamondSeparable_not_dvd_map_of_ne p h q h' hne
    rw [← heq]
    exact (hS i.1).mp i.2
  let q' : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h').map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h') q'
  let F : (E[X] ⧸ Ideal.span {poly i.1.2}) →+*
      ((AdjoinRoot (poly h'))[X] ⧸ Ideal.span {poly r.1.2}) :=
    (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h') q').toRingHom
  let g : MilnorKRing (E[X] ⧸ Ideal.span {poly i.1.2}) →+
      MilnorKRing (AdjoinRoot (poly h')) :=
    (simpleMilnorNorm r.1.2).comp (milnorKRingMap F).toAddMonoidHom
  change g (monicIrreducibleResidue i.1.2 x) = 0
  exact (congrArg g (hx.2 i.1.1 i.1.2 hne')).trans (map_zero g)

end FiniteSupport

section Diamond

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hsep hp

local notation "E" => AdjoinRoot (poly p)

/-- The original chosen rational norm contracts a genuine single-residue lift
to its actual lower native polynomial and tensor-matched quotient residue. -/
theorem IsSingleResidueLift.milnorKNorm_ratFunc_tensorSwap_of_separable
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1))
    (hx : IsSingleResidueLift q.1.2 z (x : MilnorKRing _)) :
    IsSingleResidueLift h
      (simpleMilnorNorm
        (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
        (milnorKRingMap
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom z))
      (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) := by
  constructor
  · obtain ⟨S, hS⟩ :=
      exists_finset_mem_iff_dvd_map (algebraMap k E) (poly h) (ne_zero h)
    have hfinite :=
      monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable
        p hsep hp h S hS n x
    have hsingle := primeDiamondSeparable_sum_eq_matched_of_singleLift
      p h q S hS z (x : MilnorKRing (RatFunc E)) hx
    exact hfinite.trans hsingle
  · intro e' h' hne
    obtain ⟨S, hS⟩ :=
      exists_finset_mem_iff_dvd_map (algebraMap k E) (poly h') (ne_zero h')
    have hfinite :=
      monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable
        p hsep hp h' S hS n x
    have hzero := primeDiamondSeparable_sum_eq_zero_of_singleLift
      p h q h' hne S hS z (x : MilnorKRing (RatFunc E)) hx
    exact hfinite.trans hzero

/-- The native normal-prime diamond in every homogeneous degree, including zero.
The upper factor and quotient equivalence are those of the actual tensor swap. -/
theorem simpleMilnorNorm_prime_diamond_homogeneous_of_separable
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (n : ℕ) (z : MilnorKTheory (AdjoinRoot (poly q.1.2)) n) :
    simpleMilnorNorm p
        (simpleMilnorNorm q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2)))) =
      simpleMilnorNorm h
        (simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
            (z : MilnorKRing (AdjoinRoot (poly q.1.2))))) := by
  obtain ⟨x, hx, hnorm⟩ :=
    exists_isSingleResidueLift_simpleMilnorNorm_simpleMilnorNorm_of_separable p hsep hp q.1.2 n z
  have hres := IsSingleResidueLift.milnorKNorm_ratFunc_tensorSwap_of_separable
    p hsep hp h q (z : MilnorKRing (AdjoinRoot (poly q.1.2))) n x hx
  exact hnorm.trans (simpleMilnorNorm_eq hres).symm

/-- The complete native normal-prime simple-norm diamond on the whole Milnor
K-ring. The lower polynomial and the literal upper factor are arbitrary. -/
theorem simpleMilnorNorm_prime_diamond_of_separable
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom z)) := by
  let f := (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2)
  let g := (simpleMilnorNorm h).comp
    ((simpleMilnorNorm
      (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2).comp
      (milnorKRingMap
        (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom).toAddMonoidHom)
  exact mem_of_forall_milnorKSymbolProd_mem (H := f.eqLocus g)
    (fun l => simpleMilnorNorm_prime_diamond_homogeneous_of_separable p hsep hp h q l.length
      ⟨milnorKSymbolProd _ l, milnorKSymbolProd_mem_milnorKGrading l⟩) z

/-- The diamond is equality of the original additive maps, not only an
identity for a chosen lift or a chosen homogeneous class. -/
theorem simpleMilnorNorm_comp_simpleMilnorNorm_prime_diamond_of_separable
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)}) :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        ((simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2).comp
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv
              (poly p) (poly h) q).toRingHom).toAddMonoidHom) := by
  ext z
  exact simpleMilnorNorm_prime_diamond_of_separable p hsep hp h q z

end Diamond

end Stacks.Chow

end
