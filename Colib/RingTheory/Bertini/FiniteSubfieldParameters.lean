/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.FiniteSubfieldModels
public import Colib.FieldTheory.Separable.FiniteSubfields
public import Colib.RingTheory.Bertini.QuadraticParameterTuple
/-!
# One finite stage for the same quadratic coefficients and both principal opens

The exact auxiliary coefficients a, base coefficients c, etale-near-point element r_e and
whole-fiber element r are modeled simultaneously in one actual finite separable subfield.
Both localization elements retain their individual image equations. An arbitrary previously
chosen finite scalar set may be retained, and the original field may be finite.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open IntermediateField

universe u

namespace QuadraticIncidence

/-- One actual finite subfield models the original a,c,r_e,r simultaneously, without changing
any coefficient or identifying the two principal-open choices. -/
theorem exists_finsetSubfield_quadraticParameters
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] {σ : Type u} [Finite σ] (d : ℕ)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (rₑ r : L ⊗[K] B) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      ∃ (a' : Exponent σ → adjoin K (t : Set L))
        (c' : Fin d × Exponent σ → adjoin K (t : Set L))
        (rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B),
        (∀ e, (a' e : L) = a e) ∧ (∀ q, (c' q : L) = c q) ∧
          finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r := by
  classical
  let := Fintype.ofFinite σ
  let s₀ : Finset L := s ∪ (Finset.univ.image a ∪ Finset.univ.image c)
  let v : Bool → L ⊗[K] B := fun i => if i then rₑ else r
  obtain ⟨t, ht, w, hw⟩ := exists_finsetTensor_family K L B s₀ v
  have ha (e : Exponent σ) : a e ∈ t := ht (by simp [s₀])
  have hc (q : Fin d × Exponent σ) : c q ∈ t := ht (by simp [s₀])
  refine ⟨t, (show s ⊆ s₀ from Finset.subset_union_left).trans ht,
    finite_finsetAdjoinDiagram_obj K L t,
    (fun e => ⟨a e, subset_adjoin K _ (ha e)⟩),
    (fun q => ⟨c q, subset_adjoin K _ (hc q)⟩), w true, w false,
    (fun _ => rfl), (fun _ => rfl), hw true, hw false⟩
end QuadraticIncidence
