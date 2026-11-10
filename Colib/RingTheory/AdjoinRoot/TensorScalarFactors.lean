/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.FieldTheory.Separable
import Colib.RingTheory.AdjoinRoot.Map

/-!
# The full scalar tensor product in native polynomial factors

Adapted from `Aglib/RingTheory/AdjoinRootBranchProduct.lean:36-56` and
`Aglib/RingTheory/AdjoinRootTensorBranchProduct.lean:21-40` at revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The native reduced Artinian
product is reindexed by the existing monic-irreducible sigma subtype. Each
coordinate is the original quotient factor map. No factor is omitted and no
new branch carrier, field, tensor product or norm is introduced.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped TensorProduct

namespace AdjoinRoot

variable {k : Type*} [Field k]

/-- The original quotient at a native factor, as a coefficient algebra equivalence. -/
def nativeFactorQuotientAlgEquiv (f : k[X])
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly r.2 ∣ f}) :
    (AdjoinRoot f ⧸ (nativeFactorMaximal f r).asIdeal) ≃ₐ[k]
      AdjoinRoot (poly r.1.2) :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := Ideal.Quotient.factorₐ k (Ideal.span_singleton_le_span_singleton.mpr r.2))
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr r.2))

/-- Reduction in a native factor quotient agrees with the literal factor map. -/
theorem nativeFactorQuotientAlgEquiv_mk (f : k[X])
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly r.2 ∣ f})
    (a : AdjoinRoot f) :
    nativeFactorQuotientAlgEquiv f r (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2) a := rfl

/-- A squarefree monic quotient is the product over all its actual native factors. -/
def nativeFactorProductEquiv (f : k[X]) (hf : f.Monic) (hs : Squarefree f) :
    AdjoinRoot f ≃ₐ[k]
      ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly r.2 ∣ f},
        AdjoinRoot (poly r.1.2) := by
  have : Module.Finite k (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  have : IsArtinianRing (AdjoinRoot f) := .of_finite k _
  have : IsReduced (AdjoinRoot f) := (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp hs.isRadical)
  exact ((IsArtinianRing.equivPi (AdjoinRoot f)).restrictScalars k).trans
    ((AlgEquiv.piCongrLeft k (fun m : MaximalSpectrum (AdjoinRoot f) =>
      AdjoinRoot f ⧸ m.asIdeal) (maximalFactorIndexEquiv f hf.ne_zero).symm).symm.trans
      (AlgEquiv.piCongrRight fun r => nativeFactorQuotientAlgEquiv f r))

/-- Every coordinate of the product is the actual divisor quotient map. -/
theorem nativeFactorProductEquiv_apply (f : k[X]) (hf : f.Monic) (hs : Squarefree f)
    (a : AdjoinRoot f)
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly r.2 ∣ f}) :
    nativeFactorProductEquiv f hf hs a r =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2) a := by
  have : Module.Finite k (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  have : IsArtinianRing (AdjoinRoot f) := .of_finite k _
  have : IsReduced (AdjoinRoot f) := (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp hs.isRadical)
  change nativeFactorQuotientAlgEquiv f r
    (IsArtinianRing.equivPi (AdjoinRoot f) a (nativeFactorMaximal f r)) = _
  rw [IsArtinianRing.equivPi_apply, nativeFactorQuotientAlgEquiv_mk]

variable {L : Type*} [Field L] [Algebra k L]

/-- All native scalar factors form the original full tensor product. -/
def tensorScalarFactorsEquiv {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hs : (poly p).Separable) :
    L ⊗[k] AdjoinRoot (poly p) ≃ₐ[L]
      ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
        poly r.2 ∣ (poly p).map (algebraMap k L)}, AdjoinRoot (poly r.1.2) :=
  (scalarExtensionEquiv (poly p)).trans
    (nativeFactorProductEquiv ((poly p).map (algebraMap k L))
      ((monic p).map _) hs.map.squarefree)

/-- The old field enters each component through its original coefficient quotient map. -/
theorem tensorScalarFactorsEquiv_tmul_one {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hs : (poly p).Separable) (a : AdjoinRoot (poly p))
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}) :
    tensorScalarFactorsEquiv p hs (1 ⊗ₜ[k] a) r =
      AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2 a := by
  simp only [tensorScalarFactorsEquiv, AlgEquiv.trans_apply, nativeFactorProductEquiv_apply]
  have h := RingHom.congr_fun
    (scalarExtensionEquiv_comp_includeRight (S := L) (poly p)) a
  change scalarExtensionEquiv (poly p) (1 ⊗ₜ[k] a) =
    AdjoinRoot.map (algebraMap k L) (poly p)
      ((poly p).map (algebraMap k L)) dvd_rfl a at h
  rw [h]
  obtain ⟨v, rfl⟩ := mk_surjective a
  rw [map_mk, map_mk]
  rfl

end AdjoinRoot

end
