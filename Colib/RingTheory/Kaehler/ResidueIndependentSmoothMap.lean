/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Kaehler.SmoothCotangentTrdeg
public import Colib.RingTheory.Kaehler.ResidueFunctionBasis
public import Colib.RingTheory.Etale.ResidueCoordinateCriterion

/-! # Original independent functions give a relative curve near the original prime -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential
universe u
namespace KaehlerDifferential

/-- Complete the prescribed functions by one actual original function, without changing them. -/
theorem exists_residue_basis_cons (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R] (d : ℕ) (f : Fin d → R)
    (hf : LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k])))
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ t : R, ∃ b : Basis (Fin (d + 1)) K (K ⊗[R] Ω[R⁄k]),
      ∀ i, b i = 1 ⊗ₜ[R] D k R ((Fin.cons t f : Fin (d + 1) → R) i) := by
  classical
  let v : R → K ⊗[R] Ω[R⁄k] := fun r => 1 ⊗ₜ[R] D k R r
  let W := Submodule.span K (Set.range (fun i => v (f i)))
  have hW : W ≠ ⊤ := by
    intro h
    have he := finrank_span_eq_card hf
    rw [show Submodule.span K (Set.range (fun i => v (f i))) = ⊤ from h,
      finrank_top, hd, Fintype.card_fin] at he
    omega
  have hex : ∃ t, v t ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← span_residue_original_differentials k R K]
    exact Submodule.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact h r)
  obtain ⟨t, ht⟩ := hex
  have hli : LinearIndependent K (fun i => v ((Fin.cons t f : Fin (d + 1) → R) i)) := by
    convert hf.finCons ht using 1
    ext i
    cases i using Fin.cases <;> rfl
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i => v ((Fin.cons t f : Fin (d + 1) → R) i)) hli (by simpa using hd.symm)
  exact ⟨t, b, fun i => Basis.mk_apply _ _ _⟩

end KaehlerDifferential
namespace Algebra

/-- One added function makes an étale chart in a genuine principal neighborhood;
the original first `d` functions remain its unchanged tail. -/
theorem exists_etale_cons_of_residue_independent
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ t : R, ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
      (MvPolynomial.aeval (R := k) (Fin.cons t f : Fin (d + 1) → R)).toRingHom).Etale := by
  have hrank : Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]) = d + 1 := by
    rw [cotangent_finrank_eq_trdeg_toNat k R p.ResidueField, hd]
    simp
  obtain ⟨t, b, hb⟩ := exists_residue_basis_cons k R p.ResidueField d f hf hrank
  obtain ⟨r, hr, he⟩ := exists_etale_polynomial_map_of_residue_differential_basis
    k R p (Fin.cons t f) b hb
  exact ⟨t, r, hr, he⟩

end Algebra
