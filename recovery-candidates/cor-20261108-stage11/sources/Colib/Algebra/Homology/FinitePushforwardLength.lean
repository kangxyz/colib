/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Length.FiniteAlgebraLocal
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.RingTheory.Tor.BaseChangeOfUniverse

/-!
# Residue-degree weighted homology under a finite pushforward

For a finite algebra `S` over a local ring `R`, restriction of scalars is the affine finite
pushforward. This file proves the degreewise formula for the homology of that actual functor:

`length_R H_n(Res K) = sum_q length_(S_q) H_n(K_q) * [k(q) : k(R)]`.

`K_q` is the actual complex obtained by native scalar extension to `Localization.AtPrime q`.
Restriction of scalars and localization commute with homology because they are exact. The
remaining length computation is the existing native semilocal formula, via the already owned
`Module.finiteAlgebra_length_eq_sum_tensor` interface. Neither `S/R` nor `K` is assumed flat.
In particular `S` need not be local, reduced or Artinian. The finite-length assumption is on
the homology in the degree being computed, not on the complex terms.

The signed finite-sum theorem is honest integer arithmetic: the finiteness proof precedes every
conversion from extended-natural length to an integer. It does not assert bounded Tor-amplitude,
identify a scheme-theoretic remaining support, or prove associativity of correspondences.

## References

* Stacks Project, Tag 02M0: the semilocal length and residue-degree formula, reused natively.
* Stacks Project, Tag 00M8: flat localization commutes with Tor; the same exact scalar-extension
  homology comparison is used here for an arbitrary chain complex.

The new content is their complex-level finite-pushforward combination, not a new proof of either
native provider. No additional Stacks coverage is asserted for the combination.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct

universe u

namespace Module

variable (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
  [Algebra R S] [Module.Finite R S]
variable {M : Type u} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The existing finite-algebra length formula read in integers, with finiteness of every
summand proved before applying `ENat.toNat`. -/
theorem finiteAlgebra_lengthToNat_eq_sum_tensor [Fintype (MaximalSpectrum S)]
    (hM : Module.length S M ≠ ⊤) :
    ((Module.length R M).toNat : ℤ) = ∑ q : MaximalSpectrum S,
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M)).toNat : ℤ) *
          (finiteAlgebraResidueDegree R S q : ℤ) := by
  have hlocal (q : MaximalSpectrum S) :
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) ≠ ⊤ := by
    rw [← (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).length_eq]
    exact finiteAlgebra_localized_length_ne_top R S hM q
  have h := congrArg ENat.toNat (finiteAlgebra_length_eq_sum_tensor R S hM)
  rw [ENat.toNat_sum (fun q _ =>
    WithTop.mul_ne_top (hlocal q) (ENat.natCast_ne_top _))] at h
  rw [h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]

end Module

namespace HomologicalComplex

variable (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
  [Algebra R S] [Module.Finite R S]

/-- The actual affine finite direct image of a chain complex. This is only notation for
Mathlib's restriction-of-scalars functor on complexes. -/
abbrev finitePushforwardComplex (K : ChainComplex (ModuleCat.{u} S) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj K

/-- The actual chain complex on the localization at a labelled maximal point. Distinct points
remain distinct indices, even when their image in the local base is the same closed point. -/
abbrev maximalLocalizationComplex (K : ChainComplex (ModuleCat.{u} S) ℕ)
    (q : MaximalSpectrum S) : ChainComplex (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) ℕ :=
  ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).mapHomologicalComplex
    (.down ℕ)).obj K

/-- Actual finite pushforward homology has the residue-degree weighted sum of actual localized
homology lengths. The finite map is not assumed flat. -/
theorem length_homology_finitePushforward_eq_sum [Fintype (MaximalSpectrum S)]
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (n : ℕ)
    (hK : Module.length S (K.homology n) ≠ ⊤) :
    Module.length R ((finitePushforwardComplex R S K).homology n) =
      ∑ q : MaximalSpectrum S,
        Module.length (Localization.AtPrime q.asIdeal)
          ((maximalLocalizationComplex S K q).homology n) *
            (Module.finiteAlgebraResidueDegree R S q : ℕ∞) := by
  let T := K.homology n
  let : Module R T := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := ⟨fun r s x => by
    change (r • s) • x = algebraMap R S r • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hrestrict := ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (ModuleCat.restrictScalars (algebraMap R S)) (.down ℕ) n).app K).toLinearEquiv.length_eq
  change Module.length R ((finitePushforwardComplex R S K).homology n) = _ at hrestrict
  rw [hrestrict, Module.finiteAlgebra_length_eq_sum_tensor R S hK]
  apply Finset.sum_congr rfl
  intro q _
  have hlocal := (torBaseChangeHomologyIsoOfUniverse
    (S' := Localization.AtPrime q.asIdeal) K n).toLinearEquiv.length_eq
  exact congrArg (fun l : ℕ∞ => l * (Module.finiteAlgebraResidueDegree R S q : ℕ∞)) hlocal

/-- The integer coefficient version, using the same canonical homology comparisons. -/
theorem lengthToNat_homology_finitePushforward_eq_sum [Fintype (MaximalSpectrum S)]
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (n : ℕ)
    (hK : Module.length S (K.homology n) ≠ ⊤) :
    ((Module.length R ((finitePushforwardComplex R S K).homology n)).toNat : ℤ) =
      ∑ q : MaximalSpectrum S,
        ((Module.length (Localization.AtPrime q.asIdeal)
          ((maximalLocalizationComplex S K q).homology n)).toNat : ℤ) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  let T := K.homology n
  let : Module R T := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := ⟨fun r s x => by
    change (r • s) • x = algebraMap R S r • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hrestrict := ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (ModuleCat.restrictScalars (algebraMap R S)) (.down ℕ) n).app K).toLinearEquiv.length_eq
  change Module.length R ((finitePushforwardComplex R S K).homology n) = _ at hrestrict
  rw [hrestrict, Module.finiteAlgebra_lengthToNat_eq_sum_tensor R S hK]
  apply Finset.sum_congr rfl
  intro q _
  have hlocal := (torBaseChangeHomologyIsoOfUniverse
    (S' := Localization.AtPrime q.asIdeal) K n).toLinearEquiv.length_eq
  rw [hlocal]

/-- Finite alternating homology sums commute with finite pushforward, with each original
maximal label and its original residue degree retained. No vanishing outside `degrees` is
asserted, so this is a finite Euler window rather than an unqualified Euler characteristic. -/
theorem sum_alternating_lengthToNat_homology_finitePushforward
    [Fintype (MaximalSpectrum S)] (K : ChainComplex (ModuleCat.{u} S) ℕ)
    (degrees : Finset ℕ) (hK : ∀ n ∈ degrees, Module.length S (K.homology n) ≠ ⊤) :
    (∑ n ∈ degrees, (-1 : ℤ) ^ n *
      ((Module.length R ((finitePushforwardComplex R S K).homology n)).toNat : ℤ)) =
      ∑ q : MaximalSpectrum S,
        (∑ n ∈ degrees, (-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime q.asIdeal)
            ((maximalLocalizationComplex S K q).homology n)).toNat : ℤ)) *
          (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  classical
  calc
    _ = ∑ n ∈ degrees, ∑ q : MaximalSpectrum S,
        ((-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime q.asIdeal)
            ((maximalLocalizationComplex S K q).homology n)).toNat : ℤ)) *
          (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [lengthToNat_homology_finitePushforward_eq_sum R S K n (hK n hn),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact (mul_assoc _ _ _).symm
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]

end HomologicalComplex
