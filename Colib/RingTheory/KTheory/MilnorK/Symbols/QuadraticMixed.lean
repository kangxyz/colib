/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedWitnesses

/-!
# Mixed generation for the actual quadratic root field

Every native reduced polynomial representative has degree at most one in a
quadratic extension. It therefore splits over the original coefficient field.
The existing finite-witness theorem gives the whole original mixed span, without
an auxiliary extension, perfectness, separability, or normality.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

/-- In Milnor degree one every symbol already has an empty base-field prefix. -/
theorem mem_milnorKMixedSpan_zero {k E : Type u} [Field k] [Field E]
    (φ : k →+* E) (x : MilnorKTheory E 1) : x ∈ milnorKMixedSpan φ 0 := by
  obtain ⟨c, rfl⟩ := exists_finsupp_milnorKTupleSymbol 1 x
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  have heq : Fin.snoc (Units.map φ.toMonoidHom ∘ (Fin.elim0 : Fin 0 → kˣ))
      (a 0) = a := by
    funext i
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    exact Fin.snoc_last _ _
  simpa only [heq] using milnorKTupleSymbol_snoc_mem_mixedSpan φ 0 Fin.elim0 (a 0)

variable {k : Type u} [Field k] (p : k[X]) (hp : p.Monic)
  [Fact (Irreducible p)]

include hp

/-- Every original class in a root extension of degree at most two is mixed.
In particular this includes inseparable quadratic extensions in characteristic two. -/
theorem mem_milnorKMixedSpan_of_natDegree_le_two (hdegree : p.natDegree ≤ 2)
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    x ∈ milnorKMixedSpan (algebraMap k (AdjoinRoot p)) m := by
  obtain ⟨s, hs, hgen⟩ := exists_finite_milnorK_mixed_splitting_witness p hp m x
  have hdiv : p ∣ p.map (RingHom.id k) := by simp
  have hmap : AdjoinRoot.map (RingHom.id k) p p hdiv = RingHom.id (AdjoinRoot p) := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      simp
    · simp
  have h := hgen k (RingHom.id k) p hdiv (by
    intro r hr
    rw [Polynomial.map_id]
    apply Polynomial.Splits.of_natDegree_le_one
    have := (hs r hr).2
    omega)
  simpa only [hmap, milnorKTheoryMap_id, LinearMap.id_apply] using h

/-- The existing integer mixed span is the full native homogeneous group in
quadratic degree. This identifies a submodule; it does not replace the group. -/
theorem milnorKMixedSpan_eq_top_of_natDegree_le_two (hdegree : p.natDegree ≤ 2) (m : ℕ) :
    milnorKMixedSpan (algebraMap k (AdjoinRoot p)) m = ⊤ := by
  apply top_unique
  intro x _
  exact mem_milnorKMixedSpan_of_natDegree_le_two p hp hdegree m x

end Stacks.Chow
