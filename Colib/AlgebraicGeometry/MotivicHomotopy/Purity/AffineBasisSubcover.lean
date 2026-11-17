/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite affine refinements of open covers -/

public section

open TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- Every open of a noetherian scheme is a finite union of affine opens refining the
restriction of the given finite cover. -/
theorem exists_finite_affine_subcover {X : Scheme.{u}} [IsNoetherian X] {J : Type v}
    (C : J → X.Opens) (ts : Finset J) (hc : ts.sup C = ⊤) (U : X.Opens) :
    ∃ rs : Finset X.affineOpens, rs.sup (fun W => W.1) = U ∧
      ∀ W ∈ rs, ∃ x ∈ ts, W.1 ≤ C x := by
  classical
  let I := {W : X.affineOpens // W.1 ≤ U ∧ ∃ x ∈ ts, W.1 ≤ C x}
  let D (W : I) : X.Opens := W.val.1
  have htop : (⨆ x : {x // x ∈ ts}, C x.val) = ⊤ := by
    simpa only [Finset.sup_eq_iSup, iSup_subtype] using hc
  have hsup : (⨆ W, D W) = U := by
    apply le_antisymm
    · exact iSup_le (fun W => W.property.1)
    · intro t ht
      have ht' : t ∈ (⨆ x : {x // x ∈ ts}, C x.val) :=
        htop.symm ▸ (show t ∈ (⊤ : X.Opens) from trivial)
      obtain ⟨x, hx⟩ := Opens.mem_iSup.mp ht'
      obtain ⟨W, hW, htW, hle⟩ := exists_isAffineOpen_mem_and_subset
        (show t ∈ U ⊓ C x.val from ⟨ht, hx⟩)
      have hWU : W ≤ U := fun _ hw => (hle hw).1
      have hWC : W ≤ C x.val := fun _ hw => (hle hw).2
      let W' : I := ⟨⟨W, hW⟩, hWU, ⟨x.val, x.property, hWC⟩⟩
      exact Opens.mem_iSup.mpr ⟨W', htW⟩
  have hcompact : IsCompactElement U :=
    (Opens.isCompactElement_iff _).mpr (NoetherianSpace.isCompact _)
  obtain ⟨rs, hle⟩ := (isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp hcompact
    I D (le_of_eq hsup.symm)
  have hr : rs.sup D = U := le_antisymm (Finset.sup_le fun W _ => W.property.1) hle
  refine ⟨rs.image Subtype.val, ?_, ?_⟩
  · rw [Finset.sup_image]
    exact hr
  · intro W hW
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hW
    exact V.property.2

end AlgebraicGeometry.Scheme
