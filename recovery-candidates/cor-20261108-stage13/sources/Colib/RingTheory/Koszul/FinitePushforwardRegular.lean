/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.FinitePushforward
public import Colib.RingTheory.Koszul.MappedRegularLength

/-!
# Finite pushforward of remaining Koszul Euler characteristics from geometry

The sequence is regular only in its original ambient ring. Its image generates
an ideal of definition in the Noetherian local image ring. For any finite algebra
over that image ring and any finite coefficient module, all remaining homology
lengths are proved finite. The genuine residue-degree Euler formula therefore has
no finite-length input. The finite algebra need not be flat, local, or reduced.

The finiteness argument uses the actual nonflat Koszul restriction comparison:
finite length in the local image ring bounds length over the finite algebra.
No action on abstract Tor is assumed, and the whole original signed coefficient
family is retained. The geometric ideal-of-definition input must be supplied by
the actual generic remaining intersection, not by a replacement model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

universe u

namespace Koszul

variable {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
  [Algebra A R] [Algebra R S] [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S]
  {r : ℕ}

/-- Finite remaining Koszul homology over the full finite algebra follows from
the original regular ambient list and the actual local-image colength condition. -/
theorem length_seqComplexTensor_finiteAlgebra_ne_top_of_isRegular
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} S) [Module.Finite S M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j)))))
    (n : ℕ) :
    Module.length S
      ((seqComplexTensor (fun j => algebraMap R S (algebraMap A R (f j))) M).homology n) ≠ ⊤ := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj M
  let : Module R M := N.isModule
  let : IsScalarTower R S M := .of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite R M := Module.Finite.trans S M
  have hR := length_seqComplexTensor_map_ne_top_of_isRegular f hf N hI n
  let H := (seqComplexTensor (fun j => algebraMap R S (algebraMap A R (f j))) M).homology n
  let : Module R H := Module.compHom H (algebraMap R S)
  let : IsScalarTower R S H := .of_algebraMap_smul fun _ _ => rfl
  have he := (homologySeqComplexTensorRestrictScalarsIso
    (fun j => algebraMap A R (f j)) M n).toLinearEquiv.length_eq
  change Module.length R _ = Module.length R H at he
  rw [he] at hR
  have htop := ((Submodule.topEquiv : (⊤ : Submodule S H) ≃ₗ[S] H).restrictScalars R).length_eq
  have hle := Submodule.length_le_length_restrictScalars R (⊤ : Submodule S H)
  exact ne_top_of_le_ne_top hR
    ((Module.length_top (R := S)).symm.le.trans (hle.trans htop.le))

/-- The residue-degree-weighted remaining Euler formula, with all required
finite lengths proved rather than assumed. -/
theorem seqEuler_restrictScalars_eq_sum_of_isRegular [Fintype (MaximalSpectrum S)]
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} S) [Module.Finite S M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j))))) :
    seqEuler (fun j => algebraMap A R (f j))
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ q : MaximalSpectrum S,
        seqEuler (fun j => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap R S (algebraMap A R (f j)))) (Localization.AtPrime q.asIdeal ⊗[S] M) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) :=
  seqEuler_restrictScalars_eq_sum (fun j => algebraMap A R (f j)) M
    (fun n => length_seqComplexTensor_finiteAlgebra_ne_top_of_isRegular f hf M hI n)

/-- Every signed original coefficient degree is pushed forward with its own
actual module. No fundamental-cycle or finite-length surrogate is used. -/
theorem sum_signed_seqEuler_restrictScalars_eq_sum_of_isRegular
    [Fintype (MaximalSpectrum S)]
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ℕ → ModuleCat.{u} S) [∀ b, Module.Finite S (M b)] (J : Finset ℕ)
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j))))) :
    ∑ b ∈ J, (-1 : ℤ) ^ b * seqEuler (fun j => algebraMap A R (f j))
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
      ∑ q : MaximalSpectrum S,
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          seqEuler (fun j => algebraMap S (Localization.AtPrime q.asIdeal)
            (algebraMap R S (algebraMap A R (f j))))
            (Localization.AtPrime q.asIdeal ⊗[S] M b)) *
              (Module.finiteAlgebraResidueDegree R S q : ℤ) :=
  sum_signed_seqEuler_restrictScalars_eq_sum (fun j => algebraMap A R (f j)) M J
    (fun b _ n => length_seqComplexTensor_finiteAlgebra_ne_top_of_isRegular f hf (M b) hI n)

end Koszul
