/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteSubcomplex
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Counting finite simplicial subcomplexes

Finite subcomplexes are determined by finite sets of nondegenerate
simplices. This gives the index bound for the finite realization witnesses
in Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

universe w u

namespace SSet

/-- An uncountable bound on nondegenerate simplices also bounds the
collection of finite subcomplexes of the original simplicial set. -/
theorem hasCardinalLT_finiteSubcomplexes (X : SSet.{u}) (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 < κ) (hX : HasCardinalLT X.N κ) :
    HasCardinalLT {A : X.Subcomplex // SSet.Finite A} κ := by
  classical
  have hFinset : HasCardinalLT (Finset X.N) κ := by
    rcases finite_or_infinite X.N with h | h
    · let : Fintype X.N := Fintype.ofFinite X.N
      exact hasCardinalLT_of_finite _ _ hκ.le
    · let : Infinite X.N := h
      simpa only [HasCardinalLT, Cardinal.mk_finset_of_infinite] using hX
  let code (A : {A : X.Subcomplex // SSet.Finite A}) : Finset X.N :=
    let : SSet.Finite A.val := A.property
    let : Fintype A.val.toSSet.N := Fintype.ofFinite _
    Finset.univ.image (fun s : A.val.toSSet.N =>
      SSet.N.mk (A.val.ι.app _ s.simplex)
        (by simpa only [SSet.nonDegenerate_iff_of_mono] using s.nonDegenerate))
  have hmem (A : {A : X.Subcomplex // SSet.Finite A}) (s : X.N) :
      s ∈ code A ↔ s.simplex ∈ A.val.obj _ := by
    let : SSet.Finite A.val := A.property
    let : Fintype A.val.toSSet.N := Fintype.ofFinite _
    constructor
    · intro hs
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hs
      exact t.simplex.property
    · intro hs
      obtain ⟨n, ⟨x, hx⟩, rfl⟩ := s.mk_surjective
      let t : A.val.toSSet.N := SSet.N.mk ⟨x, hs⟩
        ((A.val.mem_nonDegenerate_iff ⟨x, hs⟩).2 hx)
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩
  refine hFinset.of_injective code ?_
  intro A B e
  apply Subtype.ext
  apply le_antisymm
  · apply (SSet.Subcomplex.le_iff_contains_nonDegenerate A.val B.val).2
    intro n x hx
    let s := SSet.N.mk x.val x.property
    exact (hmem B s).1 (e ▸ (hmem A s).2 hx)
  · apply (SSet.Subcomplex.le_iff_contains_nonDegenerate B.val A.val).2
    intro n x hx
    let s := SSet.N.mk x.val x.property
    exact (hmem A s).1 (e.symm ▸ (hmem B s).2 hx)

end SSet
