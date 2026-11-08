/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FullExactness

/-!
# Residue characterization of the native polynomial filtration

The native subgroup `milnorKPolyFiltration k d` consists exactly of the classes
whose residues at monic irreducible polynomials of degree greater than `d`
vanish. Exhaustivity provides an initial stage, and the native middle-exactness
theorem descends through the stages above the chosen bound.

This works on the whole native Milnor ring, with its existing polynomial degree
filtration and residue maps. No alternative filtration or point model is used.
In positive homogeneous degree the criterion supplies the bounded part of the
rational exactness argument in `Aglib.KTheory.MilnorK.RationalExactness` at
revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The native filtration uses
degree at most `d`, whereas the source polynomial span uses degree below `d`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- Residues above the chosen polynomial degree bound vanish on the native
filtration stage. -/
theorem monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration_of_lt
    {d e : ℕ} (ψ : MonicIrreducibleOfDegree k e) (hde : d < e)
    {x : MilnorKRing (RatFunc k)} (hx : x ∈ milnorKPolyFiltration k d) :
    monicIrreducibleResidue ψ x = 0 := by
  cases e with
  | zero => exact (Nat.not_lt_zero d hde).elim
  | succ e =>
      exact monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration ψ
        (milnorKPolyFiltration_mono (Nat.le_of_lt_succ hde) hx)

/-- If all residues above `d` vanish, finite descent through the native
polynomial filtration reaches `d`. The initial bound comes from exhaustivity. -/
theorem mem_milnorKPolyFiltration_of_forall_monicIrreducibleResidue_eq_zero_above
    (d : ℕ) {x : MilnorKRing (RatFunc k)}
    (hres : ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k e),
      d < e → monicIrreducibleResidue ψ x = 0) :
    x ∈ milnorKPolyFiltration k d := by
  obtain ⟨e, he⟩ := exists_mem_milnorKPolyFiltration_ring x
  revert he
  induction e with
  | zero => exact fun he ↦ milnorKPolyFiltration_mono (Nat.zero_le d) he
  | succ e ih =>
      intro he
      by_cases hed : e + 1 ≤ d
      · exact milnorKPolyFiltration_mono hed he
      · exact ih (mem_milnorKPolyFiltration_of_forall_monicIrreducibleResidue_eq_zero he
          (fun ψ ↦ hres (e + 1) ψ (Nat.lt_of_not_ge hed)))

/-- The native degree filtration is exactly detected by the residues of higher
degree. The degree-zero stage and arbitrary, possibly inhomogeneous classes
are included. -/
theorem mem_milnorKPolyFiltration_iff_residue_eq_zero_above (d : ℕ)
    (x : MilnorKRing (RatFunc k)) :
    x ∈ milnorKPolyFiltration k d ↔
      ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k e),
        d < e → monicIrreducibleResidue ψ x = 0 :=
  ⟨fun hx _ ψ hde ↦
    monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration_of_lt ψ hde hx,
    mem_milnorKPolyFiltration_of_forall_monicIrreducibleResidue_eq_zero_above d⟩

end Stacks.Chow
