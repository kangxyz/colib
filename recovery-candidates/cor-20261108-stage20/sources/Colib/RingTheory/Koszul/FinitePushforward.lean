/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.RestrictionComparison
public import Colib.RingTheory.Koszul.GenericEuler
public import Colib.Algebra.Homology.FinitePushforwardLength

/-!
# Koszul coefficients under finite pushforward, without flatness of the finite map

For an arbitrary ring map `R → S` and an actual `S`-module `M`, the native
Koszul complex over `R` with coefficients in the restricted module is the
restriction of the native Koszul complex over `S` on the literal mapped list.
The proof combines the existing scalar-extension comparison, the native
coefficient-complex identification, and the native tensor projection formula.
No flatness, regularity, finite length, or comparison equality is an input
to this chain isomorphism.

When `R` is local and `S` is finite, finite homology length gives the original
residue-degree-weighted sum over every labelled maximal point of `S`. The
localized summands are the genuine native Koszul complexes, not an auxiliary
replacement. The signed-family theorem applies this to each original coefficient
module before summing its sign. No flatness of the finite image map is used.

The finite-length input is stated on the genuine remaining Koszul homology.
The actual generic remaining ideal-of-definition supplier is separate; this
file neither assumes nor asserts the final geometric weighted-cycle identity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

universe u

namespace Koszul

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ}

/-- Every original maximal label contributes its genuine localized Koszul
homology, weighted by its original residue degree. The finite algebra is
allowed to be nonlocal, nonreduced, and nonflat. -/
theorem lengthToNat_seqComplexTensor_restrictScalars_eq_sum
    [IsLocalRing R] [Module.Finite R S] [Fintype (MaximalSpectrum S)]
    (f : Fin r → R) (M : ModuleCat.{u} S) (n : ℕ)
    (hfin : Module.length S
      ((seqComplexTensor (fun j => algebraMap R S (f j)) M).homology n) ≠ ⊤) :
    ((Module.length R
      ((seqComplexTensor f
        ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).homology n)).toNat : ℤ) =
      ∑ q : MaximalSpectrum S,
        ((Module.length (Localization.AtPrime q.asIdeal)
          ((seqComplexTensor
            (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
            (Localization.AtPrime q.asIdeal ⊗[S] M)).homology n)).toNat : ℤ) *
              (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  let H := (seqComplexTensor (fun j => algebraMap R S (f j)) M).homology n
  let : Module R H := Module.compHom H (algebraMap R S)
  let : IsScalarTower R S H := .of_algebraMap_smul fun _ _ => rfl
  have he := (homologySeqComplexTensorRestrictScalarsIso f M n).toLinearEquiv.length_eq
  change Module.length R _ = Module.length R H at he
  rw [he, Module.finiteAlgebra_lengthToNat_eq_sum_tensor R S (M := H) hfin]
  apply Finset.sum_congr rfl
  intro q _
  obtain ⟨e⟩ := KoszulC.homology_baseChange_linearEquiv
    (S := Localization.AtPrime q.asIdeal) (fun j => algebraMap R S (f j)) M n
  rw [e.length_eq]

/-- The actual remaining Koszul Euler characteristic commutes with finite
pushforward, with every residue degree and every original label retained. -/
theorem seqEuler_restrictScalars_eq_sum [IsLocalRing R] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] (f : Fin r → R) (M : ModuleCat.{u} S)
    (hfin : ∀ n : Fin (r + 1), Module.length S
      ((seqComplexTensor (fun j => algebraMap R S (f j)) M).homology (n : ℕ)) ≠ ⊤) :
    seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ q : MaximalSpectrum S,
        seqEuler
          (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
          (Localization.AtPrime q.asIdeal ⊗[S] M) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  classical
  calc
    _ = ∑ n : Fin (r + 1), (-1 : ℤ) ^ (n : ℕ) * ∑ q : MaximalSpectrum S,
        ((Module.length (Localization.AtPrime q.asIdeal)
          ((seqComplexTensor
            (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
            (Localization.AtPrime q.asIdeal ⊗[S] M)).homology (n : ℕ))).toNat : ℤ) *
              (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
      unfold seqEuler
      apply Finset.sum_congr rfl
      intro n _
      rw [lengthToNat_seqComplexTensor_restrictScalars_eq_sum f M n (hfin n)]
    _ = _ := by
      unfold seqEuler
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => (mul_assoc _ _ _).symm

/-- Higher first-stage homology signs are retained before finite pushforward.
The actual coefficient family is never replaced by the incidence structure module. -/
theorem sum_signed_seqEuler_restrictScalars_eq_sum [IsLocalRing R] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] (f : Fin r → R) (M : ℕ → ModuleCat.{u} S) (J : Finset ℕ)
    (hfin : ∀ b ∈ J, ∀ n : Fin (r + 1), Module.length S
      ((seqComplexTensor (fun j => algebraMap R S (f j)) (M b)).homology (n : ℕ)) ≠ ⊤) :
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
      ∑ q : MaximalSpectrum S,
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          seqEuler
            (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
            (Localization.AtPrime q.asIdeal ⊗[S] M b)) *
              (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  classical
  calc
    _ = ∑ b ∈ J, (-1 : ℤ) ^ b * ∑ q : MaximalSpectrum S,
        seqEuler
          (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
          (Localization.AtPrime q.asIdeal ⊗[S] M b) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [seqEuler_restrictScalars_eq_sum f (M b) (hfin b hb)]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => (mul_assoc _ _ _).symm

end Koszul
