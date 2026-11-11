/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleInseparableTrace
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenRecursion
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Restriction of the chosen norm in any finite purely inseparable extension

Strong induction follows the literal selected recursion of `milnorKNormRing`.
The selected adjoining subfield and the remaining extension are both purely
inseparable. The simple trace formula, the induction hypothesis, and native
finrank multiplicativity give restriction after norm as multiplication by the
extension degree. The degree-one branch uses the actual inverse structure map.

This applies to the whole native Milnor ring, its additive map, and every native
homogeneous Milnor group, including degree zero. All fields share one universe.
There is no prime-degree, characteristic-zero, separability, arbitrary tower
compatibility, or injectivity hypothesis, and no substitute norm or Milnor model.
In particular, this is not cancellation of restriction and does not itself prove
transitivity of the chosen norms along arbitrary purely inseparable towers.
-/

@[expose] public noncomputable section

open Module IntermediateField

universe u

namespace Stacks.Chow

private theorem milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_aux :
    ∀ (n : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsPurelyInseparable K L] (_hn : finrank K L = n)
      (x : MilnorKRing L),
      milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
        (finrank K L : ℤ) • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K L _ _ _ _ _ hn x
    classical
    by_cases h : ∃ a : L, a ∉ Set.range (algebraMap K L)
    · have hmap (z : MilnorKRing K) :
          milnorKRingMap (algebraMap K L) z =
            milnorKRingMap (algebraMap K⟮h.choose⟯ L)
              (milnorKRingMap (algebraMap K K⟮h.choose⟯) z) := by
        rw [milnorKRingMap_comp_apply, ← IsScalarTower.algebraMap_eq K K⟮h.choose⟯ L]
      rw [milnorKNormRing_selected_step_apply h, hmap,
        milnorKRingMap_milnorKNormAdjoinSimple_of_isPurelyInseparable, map_zsmul,
        ih _ (hn ▸ finrank_adjoin_simple_lt h.choose_spec) _ _ rfl,
        smul_smul, ← Nat.cast_mul, finrank_mul_finrank K K⟮h.choose⟯ L]
    · have hb : Function.Bijective (algebraMap K L) :=
        bijective_algebraMap_of_forall h
      have hdegree : finrank K L = 1 := by
        rw [← (AlgEquiv.ofBijective (Algebra.ofId K L) hb).toLinearEquiv.finrank_eq,
          finrank_self]
      have hinv : (algebraMap K L).comp
          ((RingEquiv.ofBijective (algebraMap K L) hb).symm : L →+* K) = RingHom.id L :=
        RingHom.ext fun a => (RingEquiv.ofBijective (algebraMap K L) hb).apply_symm_apply a
      rw [milnorKNormRing_of_bijective hb, milnorKRingMap_comp_apply, hinv,
        milnorKRingMap_id_apply, hdegree, Nat.cast_one, one_zsmul]

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]

/-- Restriction after the original chosen norm of any finite purely inseparable
extension is multiplication by the degree on the entire native Milnor ring. -/
theorem milnorKRingMap_milnorKNormRing_of_isPurelyInseparable (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
      (finrank K L : ℤ) • x :=
  milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_aux _ K L rfl x

/-- The restriction-norm identity as an equality of the existing additive maps. -/
theorem milnorKRingMap_comp_milnorKNormRing_of_isPurelyInseparable :
    (milnorKRingMap (algebraMap K L)).toAddMonoidHom.comp (milnorKNormRing K L) =
      (finrank K L : ℤ) • AddMonoidHom.id (MilnorKRing L) := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKRingMap_milnorKNormRing_of_isPurelyInseparable x

/-- Restriction after the original chosen norm is multiplication by the degree
on every native homogeneous Milnor group, including degree zero. -/
theorem milnorKTransport_milnorKNorm_of_isPurelyInseparable
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x := by
  apply Subtype.ext
  exact milnorKRingMap_milnorKNormRing_of_isPurelyInseparable (x : MilnorKRing L)

/-- The homogeneous trace identity for the existing field-map linear transport. -/
theorem milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x := by
  rw [milnorKTheoryMap_eq_transport]
  exact milnorKTransport_milnorKNorm_of_isPurelyInseparable n x

/-- The homogeneous trace identity as an equality of the original additive maps. -/
theorem milnorKTransport_comp_milnorKNorm_of_isPurelyInseparable (n : ℕ) :
    (milnorKTransport (algebraMap K L) n).comp (milnorKNorm K L n) =
      (finrank K L : ℤ) • AddMonoidHom.id (MilnorKTheory L n) := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKTransport_milnorKNorm_of_isPurelyInseparable n x

end Stacks.Chow

end
