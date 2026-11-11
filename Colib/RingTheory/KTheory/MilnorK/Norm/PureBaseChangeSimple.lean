/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PurelyInseparable.MinpolyBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.ScalarFactorBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Purely inseparable base change of a native simple Milnor norm

Let `K → K' → D` be a field tower with `K' / K` purely inseparable, and let
`f : L →ₐ[K] D` be an actual embedding. If `a : L` is integral over `K` and
`f a` is separable over `K'`, restriction of the native simple norm for `K(a) / K`
is the native simple norm for `K'(f a) / K'`, preceded by the restriction induced
by `f`, and multiplied by the inseparable degree of `K(a) / K`.

The coefficient identity is the singleton case of the scalar-factor formula.
The quotient comparison uses the selected `adjoinSimpleEquivQuot` equivalences
and preserves their actual roots. There is no cancellation of an integer action,
no presentation-independence premise, and no finite-dimensional assumption on
the ambient fields. All fields have the universe required by the native Milnor
ring maps.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {K K' L D : Type u} [Field K] [Field K'] [Field L] [Field D]
  [Algebra K K'] [Algebra K L] [Algebra K D] [Algebra K' D]
  [IsScalarTower K K' D]

/-- The restriction of the supplied embedding to the actual adjoining fields,
with the coefficient field extended from `K` to `K'`. -/
def adjoinSimpleBaseChangeMap (f : L →ₐ[K] D) (a : L) :
    K⟮a⟯ →+* K'⟮f a⟯ :=
  RingHom.codRestrict (f.toRingHom.comp K⟮a⟯.val.toRingHom) K'⟮f a⟯ fun x => by
    have hle : K⟮a⟯.map f ≤ K'⟮f a⟯.restrictScalars K := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
      exact IntermediateField.adjoin_simple_le_iff.mpr
        (IntermediateField.mem_adjoin_simple_self K' (f a))
    exact hle ((IntermediateField.map_mem_map K⟮a⟯ f).mpr x.property)

@[simp]
theorem coe_adjoinSimpleBaseChangeMap (f : L →ₐ[K] D) (a : L) (x : K⟮a⟯) :
    (adjoinSimpleBaseChangeMap (K' := K') f a x : D) = f x := rfl

@[simp]
theorem adjoinSimpleBaseChangeMap_gen (f : L →ₐ[K] D) (a : L) :
    adjoinSimpleBaseChangeMap (K' := K') f a (AdjoinSimple.gen K a) =
      AdjoinSimple.gen K' (f a) := rfl

/-- Purely inseparable scalar base change, after the image of the generator
becomes separable, gives the exact inseparable-degree multiple of the new
native simple norm on the actual adjoining fields. -/
theorem milnorKNormAdjoinSimple_baseChange_of_isPurelyInseparable
    [IsPurelyInseparable K K'] (f : L →ₐ[K] D) {a : L}
    (ha : IsIntegral K a) (hsep : IsSeparable K' (f a)) (x : MilnorKRing K⟮a⟯) :
    milnorKRingMap (algebraMap K K') (milnorKNormAdjoinSimple K ha x) =
      (Field.finInsepDegree K K⟮a⟯ : ℤ) •
        milnorKNormAdjoinSimple K' (IsIntegral.map f ha).tower_top
          (milnorKRingMap (adjoinSimpleBaseChangeMap (K' := K') f a) x) := by
  classical
  let ha' : IsIntegral K' (f a) := (IsIntegral.map f ha).tower_top
  let p := minpolyOfDegree K ha
  let q := minpolyOfDegree K' ha'
  let e := adjoinSimpleEquivQuot K ha
  let e' := adjoinSimpleEquivQuot K' ha'
  let i := adjoinSimpleBaseChangeMap (K' := K') f a
  let e₀ : K⟮a⟯ ≃ₐ[K] K⟮f a⟯ :=
    (K⟮a⟯.equivMap f).trans (IntermediateField.equivOfEq (by
      rw [IntermediateField.adjoin_map, Set.image_singleton]))
  have hinsep : Field.finInsepDegree K K⟮a⟯ = Field.finInsepDegree K K⟮f a⟯ :=
    Field.finInsepDegree_eq_of_equiv K K⟮a⟯ K⟮f a⟯ e₀
  have hpmap : (poly p).map (algebraMap K K') =
      (poly q) ^ Field.finInsepDegree K K⟮a⟯ := by
    change (minpoly K a).map (algebraMap K K') =
      (minpoly K' (f a)) ^ Field.finInsepDegree K K⟮a⟯
    rw [← minpoly.algHom_eq f f.injective a, hinsep]
    exact minpoly.map_eq_pow_finInsepDegree_of_isSeparable_of_isPurelyInseparable
      K' (f a) (IsIntegral.map f ha) hsep
  have hq : poly q ∣ (poly p).map (algebraMap K K') := by
    change minpoly K' (f a) ∣ (minpoly K a).map (algebraMap K K')
    rw [← minpoly.algHom_eq f f.injective a]
    exact minpoly.dvd_map_of_isScalarTower K K' (f a)
  have hcover : ∀ (d : ℕ) (r : MonicIrreducibleOfDegree K' d),
      poly r ∣ (poly p).map (algebraMap K K') →
        ∃ j ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro d r hr
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    apply Polynomial.eq_of_monic_of_associated (monic r) (monic q)
    apply (irreducible r).associated_of_dvd (irreducible q)
    rw [hpmap] at hr
    exact (irreducible r).prime.dvd_of_dvd_pow hr
  have hmult : multiplicity (poly q) ((poly p).map (algebraMap K K')) =
      Field.finInsepDegree K K⟮a⟯ := by
    rw [hpmap]
    exact multiplicity_pow_self (ne_zero q) (irreducible q).not_isUnit _
  let j : (K[X] ⧸ Ideal.span {poly p}) →+* (K'[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map (algebraMap K K') (poly p) (poly q) hq
  have hquot : e'.symm.toRingHom.comp j = i.comp e.symm.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change e'.symm
          (AdjoinRoot.map (algebraMap K K') (poly p) (poly q) hq
            (AdjoinRoot.of (poly p) c)) = i (e.symm (AdjoinRoot.of (poly p) c))
      rw [AdjoinRoot.map_of]
      change e'.symm (algebraMap K' (K'[X] ⧸ Ideal.span {poly q}) (algebraMap K K' c)) =
        i (e.symm (algebraMap K (K[X] ⧸ Ideal.span {poly p}) c))
      rw [e'.symm.commutes, e.symm.commutes]
      apply Subtype.ext
      change algebraMap K' D (algebraMap K K' c) = f (algebraMap K L c)
      rw [← IsScalarTower.algebraMap_apply K K' D, f.commutes]
    · change e'.symm
          (AdjoinRoot.map (algebraMap K K') (poly p) (poly q) hq
            (AdjoinRoot.root (poly p))) = i (e.symm (AdjoinRoot.root (poly p)))
      rw [AdjoinRoot.map_root]
      change adjoinRootEquivAdjoin K' ha' (AdjoinRoot.root (minpoly K' (f a))) =
        i (adjoinRootEquivAdjoin K ha (AdjoinRoot.root (minpoly K a)))
      rw [adjoinRootEquivAdjoin_apply_root, adjoinRootEquivAdjoin_apply_root]
      exact (adjoinSimpleBaseChangeMap_gen (K' := K') f a).symm
  have hcomp : j.comp e.toRingHom = e'.toRingHom.comp i := by
    apply RingHom.ext
    intro z
    apply e'.symm.injective
    change e'.symm (j (e z)) = e'.symm (e' (i z))
    rw [e'.symm_apply_apply]
    change (e'.symm.toRingHom.comp j) (e z) = i z
    rw [hquot]
    change i (e.symm (e z)) = i z
    rw [e.symm_apply_apply]
  have hfactor : milnorKRingMap (algebraMap K K')
      (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) =
        (Field.finInsepDegree K K⟮a⟯ : ℤ) •
          simpleMilnorNorm q (milnorKRingMap j (milnorKRingMap e.toRingHom x)) := by
    have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors
      (algebraMap K K') p (milnorKRingMap e.toRingHom x)
      ({PUnit.unit} : Finset PUnit.{1}) (fun _ => (minpoly K' (f a)).natDegree) (fun _ => q)
      (fun b _ c _ _ => Subsingleton.elim b c) (fun _ => hq) hcover
    simpa only [Finset.sum_singleton, hmult] using h
  change milnorKRingMap (algebraMap K K')
      (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) =
    (Field.finInsepDegree K K⟮a⟯ : ℤ) •
      simpleMilnorNorm q (milnorKRingMap e'.toRingHom (milnorKRingMap i x))
  rw [hfactor, milnorKRingMap_comp_apply, hcomp, ← milnorKRingMap_comp_apply]

end Stacks.Chow

end
