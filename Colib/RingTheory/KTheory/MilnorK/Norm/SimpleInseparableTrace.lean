/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Restriction of a simple purely inseparable Milnor norm

The existing weighted scalar-factor formula computes restriction of the native
simple norm on its whole Milnor ring. In a purely inseparable presentation the
minimal polynomial has one linear factor, with its full extension multiplicity.
Native quotient evaluation and uniqueness of field maps over the base identify
the resulting composite with the identity.

The second statement uses exactly `adjoinSimpleEquivQuot` in the definition of
`milnorKNormAdjoinSimple`. No prime-degree hypothesis, separability, replacement
norm, presentation independence, or norm tower law is used. Fields have the
common universe required by the native Milnor ring. The general presentation
statement does not require a separately supplied finite-dimensional instance.

The polynomial input is Mathlib's purely inseparable minimal-polynomial theorem.
The norm input is the weighted scalar-factor formula and the degree-one quotient
formula, consequences of the Bass--Tate simple norm used for Stacks Tag 0EAY.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Restriction of a native simple norm in any purely inseparable presentation
is multiplication by the polynomial degree, on the entire Milnor ring. -/
theorem milnorKRingMap_simpleMilnorNorm_of_isPurelyInseparable
    [IsPurelyInseparable K L] {d : ℕ} (p : MonicIrreducibleOfDegree K d)
    (e : L ≃ₐ[K] (K[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L)
        (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) = (d : ℤ) • x := by
  classical
  let a : L := e.symm (AdjoinRoot.root (poly p))
  have hminpoly : poly p = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic (irreducible p)
      (AdjoinRoot.aeval_algHom_eq_zero (poly p) e.symm.toAlgHom) (monic p)
  let q : MonicIrreducibleOfDegree L 1 :=
    ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
  have hpmap : (poly p).map (algebraMap K L) = (poly q) ^ d := by
    obtain ⟨n, hn⟩ :=
      IsPurelyInseparable.minpoly_eq_X_sub_C_pow K (ringExpChar K) a
    have hdegree : d = ringExpChar K ^ n := by
      have h := congrArg Polynomial.natDegree hn
      simpa only [← hminpoly, Polynomial.natDegree_map, natDegree_eq,
        Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] using h
    rw [hminpoly, hdegree]
    exact hn
  have hd : d ≠ 0 := by
    rw [← natDegree_eq p]
    exact (irreducible p).natDegree_pos.ne'
  have hq : poly q ∣ (poly p).map (algebraMap K L) := by
    rw [hpmap]
    exact dvd_pow_self (poly q) hd
  have hcover : ∀ (rdegree : ℕ) (r : MonicIrreducibleOfDegree L rdegree),
      poly r ∣ (poly p).map (algebraMap K L) →
        ∃ i ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro rdegree r hr
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    apply Polynomial.eq_of_monic_of_associated (monic r) (monic q)
    apply (irreducible r).associated_of_dvd (irreducible q)
    rw [hpmap] at hr
    exact (irreducible r).prime.dvd_of_dvd_pow hr
  have hmult : multiplicity (poly q) ((poly p).map (algebraMap K L)) = d := by
    rw [hpmap]
    exact multiplicity_pow_self (ne_zero q) (irreducible q).not_isUnit _
  let j : (K[X] ⧸ Ideal.span {poly p}) →+* (L[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map (algebraMap K L) (poly p) (poly q) hq
  let t : (L[X] ⧸ Ideal.span {poly q}) ≃ₐ[L] L :=
    quotientSpanXSubCAlgEquiv a
  have hcomp : (t.toRingHom.comp j).comp e.toRingHom = RingHom.id L := by
    apply IsPurelyInseparable.injective_comp_algebraMap K L L
    apply RingHom.ext
    intro c
    change t (j (e (algebraMap K L c))) = algebraMap K L c
    rw [e.commutes]
    change t (AdjoinRoot.map (algebraMap K L) (poly p) (poly q) hq
      (AdjoinRoot.of (poly p) c)) = algebraMap K L c
    rw [AdjoinRoot.map_of]
    change t (algebraMap L (L[X] ⧸ Ideal.span {poly q})
      (algebraMap K L c)) = algebraMap K L c
    exact t.commutes (algebraMap K L c)
  have hfactor : milnorKRingMap (algebraMap K L)
      (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) =
        (d : ℤ) •
          simpleMilnorNorm q (milnorKRingMap j (milnorKRingMap e.toRingHom x)) := by
    have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors
      (algebraMap K L) p (milnorKRingMap e.toRingHom x)
      ({PUnit.unit} : Finset PUnit.{1}) (fun _ => 1) (fun _ => q)
      (fun i _ j _ _ => Subsingleton.elim i j) (fun _ => hq) hcover
    simpa only [Finset.sum_singleton, hmult] using h
  rw [hfactor, simpleMilnorNorm_eq_map_of_degree_one q t,
    milnorKRingMap_comp_apply, milnorKRingMap_comp_apply, hcomp,
    milnorKRingMap_id_apply]

/-- Restriction of the literal simple-adjoining norm multiplies every native
Milnor class by the degree of the actual adjoining intermediate field. -/
theorem milnorKRingMap_milnorKNormAdjoinSimple_of_isPurelyInseparable
    [IsPurelyInseparable K L] {a : L} (ha : IsIntegral K a)
    (x : MilnorKRing K⟮a⟯) :
    milnorKRingMap (algebraMap K K⟮a⟯) (milnorKNormAdjoinSimple K ha x) =
      (finrank K K⟮a⟯ : ℤ) • x := by
  change milnorKRingMap (algebraMap K K⟮a⟯)
    (simpleMilnorNorm (minpolyOfDegree K ha)
      (milnorKRingMap (adjoinSimpleEquivQuot K ha).toRingHom x)) = _
  rw [IntermediateField.adjoin.finrank ha]
  exact milnorKRingMap_simpleMilnorNorm_of_isPurelyInseparable
    (minpolyOfDegree K ha) (adjoinSimpleEquivQuot K ha) x

end Stacks.Chow

end
