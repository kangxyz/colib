/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.FinitePushforwardLength

/-!
# Finite pushforward of the actual Tor-resolution complex

For a finite algebra `S` over a local ring `R`, this file gives the residue-degree weighted
finite-fibre formula for native `CategoryTheory.Tor` over `S`. The source is the actual
`S`-linear complex obtained by tensoring the native projective resolution of `N` with `M`.
Its finite pushforward is restriction of scalars on that complex. Exact scalar restriction
identifies its homology with the restricted *same* native `S`-Tor object. Native flat base change
then identifies the localized terms with Tor over each actual `S_q`.

No `S`-action is invented on a Tor object over `R`. In particular, the theorem does NOT identify
`Tor_R(Res M, Res N)` with `Res Tor_S(M,N)`; that assertion would generally be false. No flatness
of `S/R` is required. Finite length is assumed for each actual `S`-Tor degree used in the sum,
and no bound on Tor-amplitude is manufactured.

This is the local finite-pushforward supplier for a later weighted remaining-cycle proof.
The comparison between the geometric remaining complex and this actual `S`-complex, together
with generic-support devissage, remains a separate obligation.

## References

* Stacks Project, Tag 02M0: finite-algebra residue-degree length formula, through the existing
  `Module.finiteAlgebra_length_eq_sum_tensor` interface.
* Stacks Project, Tag 00M8: native `torBaseChangeIsoOfUniverse`, used only for localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct

universe u

namespace ModuleCat.Tor

variable (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
  [Algebra R S] [Module.Finite R S]

/-- The actual tensor of `M` with the native projective resolution of `N`, over `S`. -/
abbrev resolutionTensorComplex (M N : ModuleCat.{u} S) :
    ChainComplex (ModuleCat.{u} S) ℕ :=
  ((tensorLeft M).mapHomologicalComplex (.down ℕ)).obj (projectiveResolution N).complex

/-- Restricting the actual `S`-Tor-resolution complex and taking homology gives the restriction
of the actual `S`-Tor object. The scalar structure on the right is the literal native one. -/
def finitePushforwardResolutionHomologyIso (M N : ModuleCat.{u} S) (n : ℕ) :
    (HomologicalComplex.finitePushforwardComplex R S
      (resolutionTensorComplex S M N)).homology n ≅
        (ModuleCat.restrictScalars (algebraMap R S)).obj
          (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N) :=
  (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (ModuleCat.restrictScalars (algebraMap R S)) (.down ℕ) n).app
      (resolutionTensorComplex S M N) ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      ((projectiveResolution N).isoLeftDerivedObj (tensorLeft M) n).symm

/-- The actual restricted `S`-Tor module has the weighted sum of actual local Tor lengths.
All maximal labels are retained. The finite algebra `S/R` is not required to be flat. -/
theorem length_finitePushforward_eq_sum [Fintype (MaximalSpectrum S)]
    (M N : ModuleCat.{u} S) (n : ℕ)
    (hT : Module.length S (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N) ≠ ⊤) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N)) =
      ∑ q : MaximalSpectrum S,
        Module.length (Localization.AtPrime q.asIdeal)
          (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) n).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M)).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj N)) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞) := by
  let T := ((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N
  let : Module R T := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := ⟨fun r s x => by
    change (r • s) • x = algebraMap R S r • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  change Module.length R T = _
  rw [Module.finiteAlgebra_length_eq_sum_tensor R S (M := T) hT]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun l : ℕ∞ => l * (Module.finiteAlgebraResidueDegree R S q : ℕ∞))
    (((StacksDraft.PseudoCoherence.extendScalarsTensorIso
      (S := Localization.AtPrime q.asIdeal) T).toLinearEquiv.length_eq).symm.trans
        (torBaseChangeIsoOfUniverse
          (S' := Localization.AtPrime q.asIdeal) n M N).toLinearEquiv.length_eq)

/-- Integer coefficients of the same native finite-fibre Tor formula. -/
theorem lengthToNat_finitePushforward_eq_sum [Fintype (MaximalSpectrum S)]
    (M N : ModuleCat.{u} S) (n : ℕ)
    (hT : Module.length S (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N) ≠ ⊤) :
    ((Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N))).toNat : ℤ) =
      ∑ q : MaximalSpectrum S,
        ((Module.length (Localization.AtPrime q.asIdeal)
          (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) n).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M)).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj
                N))).toNat :
              ℤ) * (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  let T := ((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N
  let : Module R T := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := ⟨fun r s x => by
    change (r • s) • x = algebraMap R S r • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  change ((Module.length R T).toNat : ℤ) = _
  rw [Module.finiteAlgebra_lengthToNat_eq_sum_tensor R S (M := T) hT]
  apply Finset.sum_congr rfl
  intro q _
  have hlocal := ((StacksDraft.PseudoCoherence.extendScalarsTensorIso
    (S := Localization.AtPrime q.asIdeal) T).toLinearEquiv.length_eq).symm.trans
      (torBaseChangeIsoOfUniverse
        (S' := Localization.AtPrime q.asIdeal) n M N).toLinearEquiv.length_eq
  rw [hlocal]

/-- The residue-degree finite-fibre formula for homology of the actual pushed Tor-resolution
complex, not for a hypothetical `S`-structure on an `R`-Tor object. -/
theorem length_finitePushforwardResolutionHomology_eq_sum [Fintype (MaximalSpectrum S)]
    (M N : ModuleCat.{u} S) (n : ℕ)
    (hT : Module.length S (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N) ≠ ⊤) :
    Module.length R ((HomologicalComplex.finitePushforwardComplex R S
      (resolutionTensorComplex S M N)).homology n) =
      ∑ q : MaximalSpectrum S,
        Module.length (Localization.AtPrime q.asIdeal)
          (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) n).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M)).obj
            ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj N)) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞) :=
  (finitePushforwardResolutionHomologyIso R S M N n).toLinearEquiv.length_eq.trans
    (length_finitePushforward_eq_sum R S M N n hT)

/-- Signed finite Euler windows of the actual pushed Tor complex, expressed by local Tor
windows and the original residue degrees. This does not assert finite Tor-amplitude. -/
theorem sum_alternating_lengthToNat_finitePushforwardResolutionHomology
    [Fintype (MaximalSpectrum S)] (M N : ModuleCat.{u} S) (degrees : Finset ℕ)
    (hT : ∀ n ∈ degrees,
      Module.length S (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj M).obj N) ≠ ⊤) :
    (∑ n ∈ degrees, (-1 : ℤ) ^ n *
      ((Module.length R ((HomologicalComplex.finitePushforwardComplex R S
        (resolutionTensorComplex S M N)).homology n)).toNat : ℤ)) =
      ∑ q : MaximalSpectrum S,
        (∑ n ∈ degrees, (-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) n).obj
              ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M)).obj
              ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj
                N))).toNat :
                ℤ)) * (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
  classical
  calc
    _ = ∑ n ∈ degrees, ∑ q : MaximalSpectrum S,
        ((-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) n).obj
              ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M)).obj
              ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj
                N))).toNat :
                ℤ)) * (Module.finiteAlgebraResidueDegree R S q : ℤ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [(finitePushforwardResolutionHomologyIso R S M N n).toLinearEquiv.length_eq,
        lengthToNat_finitePushforward_eq_sum R S M N n (hT n hn), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact (mul_assoc _ _ _).symm
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]

end ModuleCat.Tor
