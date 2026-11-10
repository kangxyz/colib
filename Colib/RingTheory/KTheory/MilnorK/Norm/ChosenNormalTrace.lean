/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
public import Colib.RingTheory.KTheory.MilnorK.Norm.SplitBaseChange
public import Mathlib.FieldTheory.Fixed

/-!
# Restriction of the chosen norm in finite normal extensions

In characteristic zero, restriction of the original chosen norm is the sum of
the actual Galois automorphism maps. The accepted finite separable presentation
and chosen-norm comparison reduce this to the native split simple-norm formula.
The presentation polynomial is the minimal polynomial of the inverse image of
its actual quotient root, so normality proves that it splits in the given field.

All fields share the universe required by the native chosen norm. The original
algebra action, quotient field and homogeneous transport are retained. No prime
degree, nontrivial-extension, chosen-presentation or norm-comparison hypothesis
is imposed. Characteristic zero supplies separability; no positive-characteristic
chosen-norm comparison is asserted.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [Normal k L] [CharZero k]

/-- Restricting the original chosen norm of a finite normal extension in
characteristic zero gives the sum over its actual base-algebra endomorphisms. -/
theorem milnorKNormRing_map_eq_sum_algHom_of_normal (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x := by
  classical
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation k L
  let e : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) :=
    { toRingEquiv := f.toRingEquiv
      commutes' := f.commutes }
  let a : L := e.symm (AdjoinRoot.root (poly p))
  have hminpoly : poly p = minpoly k a :=
    minpoly.eq_of_irreducible_of_monic (irreducible p)
      (AdjoinRoot.aeval_algHom_eq_zero (poly p) e.symm.toAlgHom) (monic p)
  have hsep : (poly p).Separable := (irreducible p).separable
  have hsplit : ((poly p).map (algebraMap k L)).Splits := by
    rw [hminpoly]
    exact Normal.splits (inferInstance : Normal k L) a
  let : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] L) :=
    PowerBasis.AlgHom.fintype (B := L) (AdjoinRoot.powerBasis' (monic p))
  calc
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
        milnorKRingMap (algebraMap k L)
          (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) :=
      congrArg (milnorKRingMap (algebraMap k L))
        (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p e x)
    _ = ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] L,
        milnorKRingMap σ.toRingHom (milnorKRingMap e.toRingHom x) :=
      simpleMilnorNorm_map_eq_sum_algHom p hsep hsplit
        (milnorKRingMap e.toRingHom x)
    _ = ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x := by
      refine Fintype.sum_equiv
        (AlgEquiv.arrowCongr e.symm (AlgEquiv.refl : L ≃ₐ[k] L) :
          ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] L) ≃ (L →ₐ[k] L)) _ _ ?_
      intro σ
      simp only [AlgEquiv.arrowCongr_apply, AlgEquiv.symm_symm,
        AlgEquiv.refl_toAlgHom, AlgHom.id_comp]
      exact milnorKRingMap_comp_apply e.toRingHom σ.toRingHom x

/-- Restriction of the original chosen norm is the actual Galois trace for
every finite normal extension in characteristic zero, including degree one. -/
theorem milnorKNormRing_map_eq_sum_gal_of_normal (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : Gal(L/k), milnorKRingMap σ.toRingHom x := by
  classical
  rw [milnorKNormRing_map_eq_sum_algHom_of_normal x]
  symm
  exact Fintype.sum_equiv (algEquivEquivAlgHom k L).toEquiv _ _ (fun _ => rfl)

/-- The original chosen norm and native homogeneous transports satisfy the
Galois trace formula in every degree, including degree zero. -/
theorem milnorKNorm_map_eq_sum_gal_of_normal (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport (algebraMap k L) n (milnorKNorm k L n x) =
      ∑ σ : Gal(L/k), milnorKTransport σ.toRingHom n x := by
  classical
  apply Subtype.ext
  change milnorKRingMap (algebraMap k L) (milnorKNormRing k L (x : MilnorKRing L)) =
    (milnorKGrading L n).subtype (∑ σ : Gal(L/k), milnorKTransport σ.toRingHom n x)
  rw [map_sum]
  exact milnorKNormRing_map_eq_sum_gal_of_normal (x : MilnorKRing L)

end Stacks.Chow

end
