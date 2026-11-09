/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.AlgebraMap
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The actual root field after rational coefficient extension

A monic irreducible polynomial over k remains irreducible over RatFunc k.
Its original mapped root field is identified with RatFunc of the original root
field. The comparison preserves the actual constants, root, and base rational
coefficient map. It is built from native liftAlgHom and finite-dimensional
bijectivity, not a second rational-function or root-field realization.

This adapts `Aglib/FieldTheory/RationalCoefficientRoot.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`. The original AdjoinRoot.map is used
directly, and no additional coefficient map or rational norm is defined.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k]

/-- A monic irreducible polynomial remains irreducible over the actual rational
function field, in arbitrary characteristic. -/
theorem Polynomial.Monic.irreducible_map_ratFunc_C {p : k[X]} (hp : p.Monic)
    (hirr : Irreducible p) : Irreducible (p.map (RatFunc.C : k →+* RatFunc k)) := by
  have hpoly : Irreducible (p.map (Polynomial.C : k →+* k[X])) := by
    apply Polynomial.Monic.irreducible_of_irreducible_map (Polynomial.evalRingHom 0)
      _ (hp.map _)
    have hcomp : (Polynomial.evalRingHom (0 : k)).comp Polynomial.C = RingHom.id k := by
      ext x
      simp
    simpa only [Polynomial.map_map, hcomp, Polynomial.map_id] using hirr
  have hfrac := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc k) (hp.map (Polynomial.C : k →+* k[X]))).mp hpoly
  simpa only [Polynomial.map_map, RatFunc.algebraMap_comp_C] using hfrac

namespace AdjoinRoot

variable (p : k[X]) [Fact (Irreducible p)]

local instance : Module.Finite k (AdjoinRoot p) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).finite

/-- Rational coefficient extension preserves the finite degree of the literal
original root field. -/
theorem finrank_ratFunc_adjoinRoot :
    Module.finrank (RatFunc k) (RatFunc (AdjoinRoot p)) = p.natDegree := by
  rw [RatFunc.finrank_ratFunc_ratFunc,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]

/-- The original mapped polynomial quotient is the rational function field of
the original root field, as an algebra over the native RatFunc k. -/
def rationalCoefficientAlgEquiv (hp : p.Monic) :
    AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) ≃ₐ[RatFunc k]
      RatFunc (AdjoinRoot p) := by
  let : Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
  let : Module.Finite (RatFunc k) (AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :=
    (hp.map _).finite_adjoinRoot
  have : Module.Finite (RatFunc k) (RatFunc (AdjoinRoot p)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [RatFunc.finrank_ratFunc_ratFunc]
      exact Module.finrank_pos)
  let f : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) →ₐ[RatFunc k]
      RatFunc (AdjoinRoot p) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (RatFunc.C (AdjoinRoot.root p)) (by
      change aeval _ (p.map (algebraMap k (RatFunc k))) = 0
      rw [aeval_map_algebraMap]
      exact AdjoinRoot.aeval_algHom_eq_zero p
        (IsScalarTower.toAlgHom k (AdjoinRoot p) (RatFunc (AdjoinRoot p))))
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) ?_).mp f.injective
  rw [(AdjoinRoot.powerBasis (hp.irreducible_map_ratFunc_C Fact.out).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, Polynomial.natDegree_map, finrank_ratFunc_adjoinRoot]

/-- The comparison sends the original new root to the constant old root. -/
@[simp]
theorem rationalCoefficientAlgEquiv_root (hp : p.Monic) :
    rationalCoefficientAlgEquiv p hp (AdjoinRoot.root (p.map RatFunc.C)) =
      RatFunc.C (AdjoinRoot.root p) := by
  have hroot : aeval (RatFunc.C (AdjoinRoot.root p))
      (p.map (algebraMap k (RatFunc k))) = 0 := by
    rw [aeval_map_algebraMap]
    exact AdjoinRoot.aeval_algHom_eq_zero p
      (IsScalarTower.toAlgHom k (AdjoinRoot p) (RatFunc (AdjoinRoot p)))
  change AdjoinRoot.liftAlgHom (p.map RatFunc.C)
    (Algebra.ofId (RatFunc k) (RatFunc (AdjoinRoot p)))
    (RatFunc.C (AdjoinRoot.root p)) hroot (AdjoinRoot.root (p.map RatFunc.C)) = _
  exact AdjoinRoot.liftAlgHom_root (p.map RatFunc.C)
    (Algebra.ofId (RatFunc k) (RatFunc (AdjoinRoot p)))
    (RatFunc.C (AdjoinRoot.root p)) hroot

/-- On every element of the old root field, the actual coefficient map becomes
the literal constant rational function. -/
theorem rationalCoefficientAlgEquiv_map (hp : p.Monic) (x : AdjoinRoot p) :
    rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl x) =
        RatFunc.C x := by
  have h : ((rationalCoefficientAlgEquiv p hp).restrictScalars k).toAlgHom.comp
      (AdjoinRoot.mapAlgHom (Algebra.ofId k (RatFunc k)) p
        (p.map (algebraMap k (RatFunc k))) dvd_rfl) =
      IsScalarTower.toAlgHom k (AdjoinRoot p) (RatFunc (AdjoinRoot p)) := by
    apply AdjoinRoot.algHom_ext
    change rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl
        (AdjoinRoot.root p)) = RatFunc.C (AdjoinRoot.root p)
    rw [AdjoinRoot.map_root, rationalCoefficientAlgEquiv_root]
  exact AlgHom.congr_fun h x

/-- The inverse comparison sends actual constant functions to the original
coefficient quotient map, on every old field element. -/
theorem rationalCoefficientAlgEquiv_symm_C (hp : p.Monic) (x : AdjoinRoot p) :
    (rationalCoefficientAlgEquiv p hp).symm (RatFunc.C x) =
      AdjoinRoot.map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl x := by
  apply (rationalCoefficientAlgEquiv p hp).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (rationalCoefficientAlgEquiv_map p hp x).symm

/-- The base-field square is the existing rational coefficient homomorphism. -/
theorem rationalCoefficientAlgEquiv_algebraMap (hp : p.Monic) (x : RatFunc k) :
    rationalCoefficientAlgEquiv p hp
      (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) x) =
      RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k (AdjoinRoot p)))
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom
          (algebraMap k (AdjoinRoot p))) x := by
  rw [AlgEquiv.commutes, RatFunc.algebraMap_eq_mapRingHom]

end AdjoinRoot
