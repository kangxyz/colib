/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Etale.ResidueCoordinateCriterion
public import Colib.RingTheory.Kaehler.PrimeParameterDifferential
public import Colib.RingTheory.Kaehler.ResidueFunctionBasis
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Option
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# Étale line charts with a parameter in the original prime ideal

An original prime element with nonzero residue differential extends to a
finite basis of differentials of original functions. The native residue
coordinate criterion makes their polynomial map étale on a principal open.
Splitting off the chosen coordinate identifies it with the literal line
variable over the polynomial algebra in the remaining coordinates.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/RingTheory/Etale/PrimeParameter/{Chart,Line}.lean` and
`Motivic/Aglib/RingTheory/Kaehler/PrescribedResidueFunctionBasis.lean`.
-/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential

universe u v w

namespace KaehlerDifferential

private theorem exists_residue_basis_original_functions_containing
    (k : Type u) (R : Type v) (K : Type w)
    [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra.EssFiniteType k R] (f : R)
    (hf : (1 ⊗ₜ[R] D k R f : K ⊗[R] Ω[R⁄k]) ≠ 0) :
    ∃ (s : Set R), s.Finite ∧ f ∈ s ∧
      ∃ b : Basis s K (K ⊗[R] Ω[R⁄k]), ∀ j, b j = 1 ⊗ₜ[R] D k R j := by
  let v : R → K ⊗[R] Ω[R⁄k] := fun x ↦ 1 ⊗ₜ[R] D k R x
  have hv : Submodule.span K (Set.range v) = ⊤ := span_residue_original_differentials k R K
  have hli : LinearIndepOn K v {f} := (linearIndepOn_singleton_iff K).mpr hf
  let s := hli.extend (Set.subset_univ {f})
  have hsp : Submodule.span K (Set.range (fun j : s ↦ v j)) = ⊤ := by
    rw [show Set.range (fun j : s ↦ v j) = v '' s from by
      ext z
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]]
    rw [hli.span_image_extend_eq_span_image, Set.image_univ, hv]
  let b : Basis s K (K ⊗[R] Ω[R⁄k]) := Basis.mk (hli.linearIndepOn_extend _) hsp.ge
  have : Finite s := Module.Finite.finite_basis b
  exact ⟨s, Set.toFinite s, hli.subset_extend _ (Set.mem_singleton f),
    b, fun _ ↦ Basis.mk_apply _ _ _⟩

end KaehlerDifferential

namespace Algebra

/-- At a positive dimensional prime of a smooth algebra over a perfect field,
the original prime element becomes the literal line variable on a principal open. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/RingTheory/Etale/PrimeParameter/Line.lean:21-36"
  "adaptation" "The same prime element, principal neighborhood and étale line coordinate"]
theorem exists_prime_parameter_etale_line_chart
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ f ∈ p, ∃ (d : ℕ) (i : Fin d), ∃ r ∉ p,
      ∃ ψ : Polynomial (MvPolynomial {j : Fin d // j ≠ i} k) →ₐ[k] Localization.Away r,
        ψ.toRingHom.Etale ∧ ψ Polynomial.X = algebraMap R (Localization.Away r) f := by
  classical
  let : IsRegularRing R := Algebra.isRegularRing_of_smooth k R
  let : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization p _
  let K := IsLocalRing.ResidueField (Localization.AtPrime p)
  obtain ⟨f, hfp, hf⟩ := exists_prime_residue_differential_ne_zero k R p hpos
  obtain ⟨s, hs, hfs, b, hb⟩ := exists_residue_basis_original_functions_containing k R K f hf
  let := hs.fintype
  let d := Fintype.card s
  let e : s ≃ Fin d := Fintype.equivFin s
  let g : Fin d → R := fun j ↦ (e.symm j).val
  let i : Fin d := e ⟨f, hfs⟩
  let bK := b.reindex e
  have hbK (j : Fin d) : bK j = 1 ⊗ₜ[R] D k R (g j) := by
    simpa only [bK, Basis.reindex_apply, g] using hb (e.symm j)
  have hgi : g i = f := congrArg Subtype.val (e.symm_apply_apply ⟨f, hfs⟩)
  obtain ⟨r, hr, hφ⟩ := exists_etale_polynomial_map_of_residue_differential_basis k R p g bK hbK
  let φ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away r :=
    (IsScalarTower.toAlgHom k R (Localization.Away r)).comp (MvPolynomial.aeval g)
  let t := (MvPolynomial.optionEquivLeft k {j : Fin d // j ≠ i}).symm.trans
    (MvPolynomial.renameEquiv k (Equiv.optionSubtypeNe i))
  let ψ := φ.comp t.toAlgHom
  refine ⟨f, hfp, d, i, r, hr, ψ, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition t.toRingHom φ.toRingHom
      (RingHom.Etale.of_bijective t.bijective) hφ
  · change φ (t Polynomial.X) = _
    have ht : t Polynomial.X = MvPolynomial.X i := by
      simp only [t, AlgEquiv.trans_apply, MvPolynomial.optionEquivLeft_symm_X,
        MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.optionSubtypeNe_none]
    rw [ht]
    change algebraMap R (Localization.Away r)
      ((MvPolynomial.aeval (R := k) g) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X, hgi]

end Algebra
