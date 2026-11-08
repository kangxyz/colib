/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Length.FiniteAlgebraLocal
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Finite field extension after a nonreduced local base change

For a finite field extension `L/K` and a local Artinian `K`-algebra `R`, the
entire algebra `R ⊗[K] L` is kept. Its maximal local factors can split and can
be nonreduced. Their lengths weighted by the actual local residue degrees sum
to `[L : K] * length_R R`, not just `[L : K]`.

The proof directly combines native flat-local length (Stacks 02M1) with the
native finite-algebra all-point length formula (Stacks 02M0). The first is used
along the field-to-local-ring map; the second is used on the actual tensor
algebra. No separability, perfectness, reduction, or enumeration of branches is
assumed. This supplies the algebraic weight identity for exterior base-change
regrouping. Its actual scheme-stalk and generic-label identifications are
separate geometric obligations.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Module

variable (K : Type u) (L : Type v) (R : Type w)
  [Field K] [Field L] [Algebra K L] [Module.Finite K L]
  [CommRing R] [IsLocalRing R] [Algebra K R]

/-- Flat-local length over the field keeps the complete local base multiplicity. -/
theorem length_tensor_fieldExtension :
    Module.length R (R ⊗[K] L) = (Module.finrank K L : ℕ∞) * Module.length R R := by
  rw [IsLocalRing.length_baseChange K R L, Module.length_eq_finrank K L,
    IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot,
    (AlgEquiv.quotientBot R R).toLinearEquiv.length_eq]

/-- All local tensor branches, weighted by their actual residue degrees, recover the original
field degree times the full nonreduced local base length. -/
theorem finsum_length_mul_residueDegree_tensor_fieldExtension [IsArtinianRing R] :
    ∑ᶠ q : MaximalSpectrum (R ⊗[K] L),
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
        (Module.finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℕ∞) =
      (Module.finrank K L : ℕ∞) * Module.length R R := by
  let B := R ⊗[K] L
  let : IsArtinianRing B := IsArtinianRing.of_finite R B
  have he := Module.finiteAlgebra_length_eq_finsum_tensor R B (M := B)
    (Module.length_ne_top (R := B) (M := B))
  have hsum : Module.length R B =
      ∑ᶠ q : MaximalSpectrum B,
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
          (Module.finiteAlgebraResidueDegree R B q : ℕ∞) := by
    refine he.trans (finsum_congr fun q => ?_)
    rw [(TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).length_eq]
  exact hsum.symm.trans (length_tensor_fieldExtension K L R)

/-- The same branch identity in integers; Artinianness proves every length finite before
conversion, and the target multiplicity is still present. -/
theorem finsum_natCast_length_mul_residueDegree_tensor_fieldExtension [IsArtinianRing R] :
    ∑ᶠ q : MaximalSpectrum (R ⊗[K] L),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) *
        (Module.finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℤ) =
      (Module.finrank K L : ℤ) * ((Module.length R R).toNat : ℤ) := by
  classical
  let B := R ⊗[K] L
  let : IsArtinianRing B := IsArtinianRing.of_finite R B
  let : Finite (MaximalSpectrum B) := Module.finiteAlgebra_maximalSpectrum_finite R B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have he := finsum_length_mul_residueDegree_tensor_fieldExtension K L R
  rw [finsum_eq_sum_of_fintype] at he ⊢
  have hn := congrArg ENat.toNat he
  rw [ENat.toNat_sum (s := Finset.univ)
    (f := fun q : MaximalSpectrum B =>
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
        (Module.finiteAlgebraResidueDegree R B q : ℕ∞)) (fun q _ =>
      WithTop.mul_ne_top (Module.length_ne_top (R := Localization.AtPrime q.asIdeal)
        (M := Localization.AtPrime q.asIdeal)) (ENat.natCast_ne_top _))] at hn
  simp only [ENat.toNat_mul, ENat.toNat_natCast] at hn
  exact_mod_cast hn

end Module
