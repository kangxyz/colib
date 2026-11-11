/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFiniteResiduePure
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalPureOrigin
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeInseparableChosenComparison
import Colib.RingTheory.Polynomial.FactorContraction

/-!
# The native simple-norm diamond in purely inseparable prime degree

The infinity square computes the first iterated norm on an upper single-residue
lift. The finite-place formula takes the same lift to the original lower point,
with its tensor-matched residue. The simple norm of this lower lift gives the
other iterated norm. The argument applies in every homogeneous degree.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

local instance primeDiamondPure_irreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance primeDiamondPure_finiteRoot {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (monic p).finite_adjoinRoot

local instance primeDiamondPure_finiteRatFunc {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d)

local notation "E" => AdjoinRoot (poly p)

private theorem exists_primeDiamondPure_factor (h : MonicIrreducibleOfDegree k e) :
    Nonempty {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)} := by
  have hg : ¬IsUnit ((poly h).map (algebraMap k E)) := by
    intro hu
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_map] at hdeg
    exact (ne_of_gt (irreducible h).natDegree_pos) hdeg
  obtain ⟨q, hi, hq⟩ := WfDvdMonoid.exists_irreducible_factor hg
    ((monic h).map (algebraMap k E)).ne_zero
  let r : MonicIrreducibleOfDegree E (normalize q).natDegree :=
    ⟨normalize q, Polynomial.monic_normalize hi.ne_zero,
      (normalize_associated q).irreducible_iff.mpr hi, rfl⟩
  exact ⟨⟨⟨_, r⟩, normalize_dvd_iff.mpr hq⟩⟩

variable (hp : d.Prime) [hPure : IsPurelyInseparable k (AdjoinRoot (poly p))]

include hp hPure

private theorem simpleMilnorNorm_simpleMilnorNorm_eq_neg_infinityResidueRing_of_lift_of_pure
    {f : ℕ} (q : MonicIrreducibleOfDegree E f)
    (z : MilnorKRing (E[X] ⧸ Ideal.span {poly q})) (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1))
    (hx : IsSingleResidueLift q z (x : MilnorKRing (RatFunc E))) :
    simpleMilnorNorm p (simpleMilnorNorm q z) =
      -infinityResidueRing k
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) := by
  have hinf := congrArg (fun a : MilnorKTheory k n => (a : MilnorKRing k))
    (infinityResidue_milnorKNorm_ratFunc_of_isPurelyInseparable p hp n x)
  simp only [coe_infinityResidue, coe_milnorKNorm] at hinf
  have hd : Nat.Prime (Module.finrank k E) := by
    rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank, AdjoinRoot.powerBasis_dim, natDegree_eq p]
    exact hp
  let ε : E ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) :=
    { toRingEquiv := RingEquiv.refl _, commutes' := fun _ => rfl }
  let y : MilnorKRing E := infinityResidueRing E x
  have hcomparison :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable hd p ε y
  change milnorKNormRing k E y = simpleMilnorNorm p (milnorKRingMap (RingHom.id E) y)
    at hcomparison
  have hnorm : milnorKNormRing k E y = simpleMilnorNorm p y := by
    simpa only [milnorKRingMap_id_apply] using hcomparison
  have hq : (simpleMilnorNorm q z : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) = -y :=
    simpleMilnorNorm_eq hx
  exact (congrArg (simpleMilnorNorm p) hq).trans ((map_neg (simpleMilnorNorm p) y).trans
    ((congrArg Neg.neg hnorm.symm).trans (congrArg Neg.neg hinf.symm)))

variable (h : MonicIrreducibleOfDegree k e)

local notation "matched" q => AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
local notation "swap" q => AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q

private theorem IsSingleResidueLift.milnorKNorm_ratFunc_tensorSwap_of_pure
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (z : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2})) (n : ℕ)
    (x : MilnorKTheory (RatFunc E) (n + 1))
    (hx : IsSingleResidueLift q.1.2 z (x : MilnorKRing (RatFunc E))) :
    IsSingleResidueLift h
      (simpleMilnorNorm (matched q).1.2 (milnorKRingMap (swap q).toRingHom z))
      (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) := by
  constructor
  · let F : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
        ((AdjoinRoot (poly h))[X] ⧸ Ideal.span {poly (matched q).1.2}) := (swap q).toRingHom
    let g := (simpleMilnorNorm (matched q).1.2).comp (milnorKRingMap F).toAddMonoidHom
    have hfinite :=
      monicIrreducibleResidue_milnorKNorm_ratFunc_eq_tensorSwap_of_isPurelyInseparable p hp h q n x
    exact hfinite.trans (congrArg g hx.1)
  · intro e' h' hne
    obtain ⟨q'⟩ := exists_primeDiamondPure_factor p h'
    have hneq : poly q'.1.2 ≠ poly q.1.2 := by
      intro heq
      have hdiv : poly q.1.2 ∣ (poly h').map (algebraMap k E) := heq ▸ q'.2
      have hd : poly h ∣ poly h' :=
        (Polynomial.dvd_map_iff_of_dvd_irreducible_map (algebraMap k E)
          (irreducible h) (irreducible q.1.2).not_isUnit q.2 (poly h')).mp hdiv
      exact hne (Polynomial.eq_of_monic_of_associated (monic h) (monic h')
        ((irreducible h).associated_of_dvd (irreducible h') hd)).symm
    let r' := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h') q'
    let F : (E[X] ⧸ Ideal.span {poly q'.1.2}) →+*
        ((AdjoinRoot (poly h'))[X] ⧸ Ideal.span {poly r'.1.2}) :=
      (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h') q').toRingHom
    let g := (simpleMilnorNorm r'.1.2).comp (milnorKRingMap F).toAddMonoidHom
    have hfinite := monicIrreducibleResidue_milnorKNorm_ratFunc_eq_tensorSwap_of_isPurelyInseparable
      p hp h' q' n x
    exact hfinite.trans ((congrArg g (hx.2 _ q'.1.2 hneq)).trans (map_zero g))

private theorem simpleMilnorNorm_prime_diamond_homogeneous_of_pure
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (n : ℕ) (z : MilnorKTheory (E[X] ⧸ Ideal.span {poly q.1.2}) n) :
    simpleMilnorNorm p
        (simpleMilnorNorm q.1.2 (z : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2}))) =
      simpleMilnorNorm h
        (simpleMilnorNorm (matched q).1.2
          (milnorKRingMap (swap q).toRingHom
            (z : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2})))) := by
  let zq : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2}) :=
    (z : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2}))
  have hzq : zq ∈ milnorKGrading (E[X] ⧸ Ideal.span {poly q.1.2}) n := z.property
  obtain ⟨y, hydeg, hy⟩ := exists_isSingleResidueLift' q.1.2 hzq
  let x : MilnorKTheory (RatFunc E) (n + 1) := ⟨y, hydeg⟩
  have hinf := simpleMilnorNorm_simpleMilnorNorm_eq_neg_infinityResidueRing_of_lift_of_pure
    p hp q.1.2 zq n x hy
  have hres := IsSingleResidueLift.milnorKNorm_ratFunc_tensorSwap_of_pure p hp h q zq n x hy
  exact hinf.trans (simpleMilnorNorm_eq hres).symm

/-- The native simple-norm diamond for a purely inseparable prime-degree
constant extension, with its original tensor-swap quotient equivalence. -/
theorem simpleMilnorNorm_prime_diamond_of_isPurelyInseparable
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (simpleMilnorNorm (matched q).1.2 (milnorKRingMap (swap q).toRingHom z)) := by
  let f := (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2)
  let g := (simpleMilnorNorm h).comp
    ((simpleMilnorNorm (matched q).1.2).comp (milnorKRingMap (swap q).toRingHom).toAddMonoidHom)
  exact mem_of_forall_milnorKSymbolProd_mem (H := f.eqLocus g)
    (fun l => simpleMilnorNorm_prime_diamond_homogeneous_of_pure p hp h q l.length
      ⟨milnorKSymbolProd _ l, milnorKSymbolProd_mem_milnorKGrading l⟩) z

end Stacks.Chow

end
