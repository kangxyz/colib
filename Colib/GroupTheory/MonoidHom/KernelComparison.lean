/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # A displayed comparison between two surjective group quotients -/

@[expose] public section
universe u v w

namespace MonoidHom
variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

/-- A supplied factor map between surjections with equal kernels is bijective.
This is nonabelian and does not assert existence of the factor map. -/
theorem bijective_of_surjective_equal_kernels (f : G →* H) (g : G →* K) (h : H →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) (hcomm : h.comp f = g) : Function.Bijective h := by
  constructor
  · apply (injective_iff_map_eq_one h).mpr
    intro b hb
    obtain ⟨a, rfl⟩ := hf b
    have hga : g a = 1 := by
      rw [← hcomm]
      exact hb
    have ha : a ∈ g.ker := hga
    rw [← hker] at ha
    exact ha
  · intro c
    obtain ⟨a, ha⟩ := hg c
    refine ⟨f a, ?_⟩
    change (h.comp f) a = c
    rw [hcomm]
    exact ha


attribute [colib_ref "quillen"
  "Quillen/Aglib/Algebra/Group/Hom/KernelComparison.lean:20-38"
  "adaptation" "The given commuting factor between nonabelian surjections with the same kernel"]
  bijective_of_surjective_equal_kernels

end MonoidHom
