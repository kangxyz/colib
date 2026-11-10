/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# The original degree-one rational norm at every linear finite place

The actual rational coefficient algebra map of an original degree-one root field
is bijective. Its native chosen norm is therefore inverse restriction. Polynomial
residue naturality, with the actual linear factor multiplicity proved equal to one,
and the exact quotient evaluation square give the norm-residue square.

Both the whole-ring theorem and its homogeneous specialization retain the original
root field, native chosen norms, original linear points, and actual quotient maps.
There are no characteristic, normality, prime-degree, or compatibility hypotheses.
No field, rational coefficient map, residue, or norm is defined here. This supplies
the degree-one branch, not a finite-place sum or a norm tower theorem.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u v

namespace Polynomial

/-- The actual coefficient map on linear polynomial quotients commutes with
native evaluation. The square is proved on all polynomial classes. -/
theorem quotientSpanXSubCAlgEquiv_comp_adjoinRoot_map
    {k : Type u} [Field k] {K : Type v} [Field K] (φ : k →+* K) (a : k)
    (h : X - C (φ a) ∣ (X - C a).map φ) :
    (quotientSpanXSubCAlgEquiv (φ a)).toRingHom.comp
        (AdjoinRoot.map φ (X - C a) (X - C (φ a)) h) =
      φ.comp (quotientSpanXSubCAlgEquiv a).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change quotientSpanXSubCAlgEquiv (φ a)
      (AdjoinRoot.map φ (X - C a) (X - C (φ a)) h
        (AdjoinRoot.mk (X - C a) r)) =
    φ (quotientSpanXSubCAlgEquiv a (AdjoinRoot.mk (X - C a) r))
  rw [AdjoinRoot.map_mk]
  change (r.map φ).eval (φ a) = φ (r.eval a)
  exact Polynomial.eval_map_apply φ a

end Polynomial

local instance rationalDegreeOne_isMaximal_span_X_sub_C
    {K : Type u} [Field K] (b : K) :
    (Ideal.span ({X - C b} : Set K[X])).IsMaximal :=
  Stacks.Chow.isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C b)

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Evaluating the original linear residues turns coefficient restriction into
literal restriction on coefficient fields. The actual multiplicity is one. -/
theorem monicIrreducibleResidue_X_sub_C_mapRingHom
    (φ : k →+* K) (a : k) (x : MilnorKRing (RatFunc k)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv (φ a)).toRingHom
        (monicIrreducibleResidue
          (⟨X - C (φ a), monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
            MonicIrreducibleOfDegree K 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap φ
        (milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
          (monicIrreducibleResidue
            (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
              MonicIrreducibleOfDegree k 1) x)) := by
  let q : MonicIrreducibleOfDegree k 1 :=
    ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
  let r : MonicIrreducibleOfDegree K 1 :=
    ⟨X - C (φ a), monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩
  have hmap : (poly q).map φ = poly r := by
    change (X - C a).map φ = X - C (φ a)
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hdiv : poly r ∣ (poly q).map φ := by
    simpa only [hmap] using (dvd_rfl : poly r ∣ poly r)
  have hmult : multiplicity (poly r) ((poly q).map φ) = 1 := by
    rw [hmap]
    exact (irreducible r).multiplicity_self
  have hres := monicIrreducibleResidue_mapRingHom φ q r hdiv x
  rw [hmult, Nat.cast_one, one_zsmul] at hres
  calc
    _ = milnorKRingMap (quotientSpanXSubCAlgEquiv (φ a)).toRingHom
        (milnorKRingMap (AdjoinRoot.map φ (poly q) (poly r) hdiv)
          (monicIrreducibleResidue q x)) :=
      congrArg (milnorKRingMap (quotientSpanXSubCAlgEquiv (φ a)).toRingHom) hres
    _ = _ := by
      let f : (k[X] ⧸ Ideal.span {poly q}) →+* (K[X] ⧸ Ideal.span {poly r}) :=
        AdjoinRoot.map φ (poly q) (poly r) hdiv
      let g : (K[X] ⧸ Ideal.span {poly r}) →+* K :=
        (quotientSpanXSubCAlgEquiv (φ a)).toRingHom
      let e : (k[X] ⧸ Ideal.span {poly q}) →+* k :=
        (quotientSpanXSubCAlgEquiv a).toRingHom
      let z : MilnorKRing (k[X] ⧸ Ideal.span {poly q}) := monicIrreducibleResidue q x
      have hleft : milnorKRingMap g (milnorKRingMap f z) =
          milnorKRingMap (g.comp f) z :=
        milnorKRingMap_comp_apply f g z
      have hsquare : g.comp f = φ.comp e :=
        quotientSpanXSubCAlgEquiv_comp_adjoinRoot_map φ a hdiv
      have hmiddle : milnorKRingMap (g.comp f) z = milnorKRingMap (φ.comp e) z :=
        congrArg (fun j : (k[X] ⧸ Ideal.span {poly q}) →+* K => milnorKRingMap j z)
          hsquare
      have hright : milnorKRingMap φ (milnorKRingMap e z) =
          milnorKRingMap (φ.comp e) z :=
        milnorKRingMap_comp_apply e φ z
      exact hleft.trans (hmiddle.trans hright.symm)

variable (p : MonicIrreducibleOfDegree k 1)

local instance rationalDegreeOne_factIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalDegreeOne_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalDegreeOne_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

/-- The actual rational coefficient algebra map is bijective for the literal
original degree-one root field, in arbitrary characteristic. -/
theorem algebraMap_ratFunc_adjoinRoot_bijective_of_degree_one :
    Function.Bijective
      (algebraMap (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq]

/-- On every whole-ring class, the native linear residue of the original chosen
rational norm is the original coefficient norm of the native upper residue. -/
theorem monicIrreducibleResidue_X_sub_C_milnorKNormRing_ratFunc_of_degree_one
    (a : k) (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree k 1)
          (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x)) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1) x)) := by
  let z := milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x
  have hb := algebraMap_ratFunc_adjoinRoot_bijective_of_degree_one p
  have hx : milnorKRingMap
      (algebraMap (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) z = x := by
    dsimp only [z]
    rw [milnorKNormRing_of_bijective hb]
    let g := RingEquiv.ofBijective
      (algebraMap (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) hb
    change milnorKRingMap (g : RatFunc k →+* RatFunc (AdjoinRoot (poly p)))
      (milnorKRingMap (g.symm : RatFunc (AdjoinRoot (poly p)) →+* RatFunc k) x) = x
    rw [milnorKRingMap_comp_apply, RingEquiv.comp_symm, milnorKRingMap_id_apply]
  have hdim : Module.finrank k (AdjoinRoot (poly p)) = 1 := by
    rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_eq]
  have hres := monicIrreducibleResidue_X_sub_C_mapRingHom
    (algebraMap k (AdjoinRoot (poly p))) a z
  rw [← RatFunc.algebraMap_eq_mapRingHom, hx] at hres
  calc
    _ = milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap (algebraMap k (AdjoinRoot (poly p)))
          (milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
            (monicIrreducibleResidue
              (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
                MonicIrreducibleOfDegree k 1) z))) := by
      rw [milnorKNormRing_milnorKRingMap, hdim, Nat.cast_one, one_zsmul]
    _ = _ := congrArg (milnorKNormRing k (AdjoinRoot (poly p))) hres.symm

/-- The homogeneous degree-one branch has precisely the original native
linear-place norm-residue square, without a normality or characteristic hypothesis. -/
theorem monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_degree_one
    (a : k) (n : ℕ) (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree k 1)
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
            (n + 1) x : MilnorKRing (RatFunc k))) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))))) :=
  monicIrreducibleResidue_X_sub_C_milnorKNormRing_ratFunc_of_degree_one p a x

end Stacks.Chow
